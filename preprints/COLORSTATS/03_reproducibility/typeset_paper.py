"""Typeset the color-statistics paper (EN and ES) through the series layout.

The Markdown files in 01_manuscript are the semantic source. The layout files in
03_reproducibility/layout are copied unchanged from the GHHSBRIDGE note (itself from
Latinon preprint 1.0). Pandoc converts the body only; the title block comes from the
Markdown front matter (title, author, edition, DOI and repository lines) and the preamble
from the series layout. Each PDF is compiled twice with Tectonic. Logs go to
02_validation/typesetting. Adapted from GHHSBRIDGE 03_reproducibility/typeset_note.py.

Usage: python -I typeset_paper.py [en] [es]   (default: every language whose Markdown exists)
"""
from pathlib import Path
import subprocess, re, shutil, hashlib, datetime, json, os, sys

base = Path(__file__).resolve().parents[1]
man = base/'01_manuscript'
logs = base/'02_validation/typesetting'
logs.mkdir(parents=True, exist_ok=True)
pandoc = shutil.which('pandoc') or str(Path.home()/'.cache/nw-typesetting/pandoc/pandoc-3.12.1/pandoc.exe')
tectonic = shutil.which('tectonic') or str(Path.home()/'.cache/nw-typesetting/tectonic/tectonic.exe')
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()

tmp = Path(os.environ.get('TEMP', str(Path.home())))/'colorstats_typeset'
tmp.mkdir(exist_ok=True)
fontenv = os.environ.copy()
fontconfig = tmp/'fontconfig.xml'
fontconfig.write_text('<?xml version="1.0"?>\n<fontconfig><dir>C:/Windows/Fonts</dir><cachedir>'
                      + str(tmp/'fontcache').replace('\\', '/') + '</cachedir></fontconfig>\n', encoding='utf-8')
fontenv['FONTCONFIG_FILE'] = str(fontconfig)

LANG = {
    'en': {'heads': 'Theorem|Lemma|Corollary|Proposition|Claim|Remark|Definition',
           'refs': 'References', 'affil': 'Independent researcher, Santiago, Chile', 'babel': 'en'},
    'es': {'heads': 'Teorema|Lema|Corolario|Proposición|Afirmación|Observación|Definición',
           'refs': 'Referencias', 'affil': 'Investigador independiente, Santiago, Chile', 'babel': 'es'},
}
stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')


def front_block(lines):
    """Render the edition, DOI and repository lines of the Markdown front matter."""
    out = []
    for line in lines:
        line = line.strip()
        if not line or line == '---':
            continue
        m = re.match(r'^(.*?)(https?://\S+?)(\.?)$', line)
        if m:
            out.append(m.group(1) + r'\url{' + m.group(2) + '}' + m.group(3))
        else:
            out.append(r'\textbf{' + line.replace('—', '---') + '}')
    return '\\\\\n'.join(out)


def inline_code(match):
    value = match.group(1)
    if ' ' in value:
        return r'\texttt{' + value + '}'
    plain = value.replace(r'\_', '_').replace(r'\textquotesingle{}', "'")
    if len(plain) <= 18 and '/' not in plain:
        return r'\mbox{\path{' + plain + '}}'
    return r'\path{' + plain + '}'


def build(lang):
    L = LANG[lang]
    source = man/f'color_stats_{lang}.md'
    md = source.read_text(encoding='utf-8')
    assert '\t' not in md and '\b' not in md
    lines = md.splitlines()
    title = lines[0].removeprefix('# ')
    head = md[:md.index('\n## ')].splitlines()
    assert head[2] == 'Juan Pablo Traverso Gianini', head[:3]
    front = front_block(head[3:])
    body = md[md.index('\n## ') + 1:]
    conv = subprocess.run([pandoc, '--from=markdown+tex_math_dollars', '--to=latex', '--wrap=none'],
                          input=body, text=True, encoding='utf-8', capture_output=True, check=True)
    texbody = conv.stdout
    texbody = re.sub(r'\\texttt\{((?:[^{}]|\\textquotesingle\{\})+)\}', inline_code, texbody)
    texbody = re.sub(r'\\textbf\{((?:' + L['heads'] + r') [^{}]+)\}',
                     lambda m: r'\Needspace{7\baselineskip}\textbf{' + m.group(1) + '}', texbody)
    texbody = texbody.replace('\n\\[', '\n\\nopagebreak[4]\n\\[')
    texbody = texbody.replace(r' \(\square\)', r'~\(\square\)')
    if lang == 'es':
        # babel-spanish typesets \roman in (faked) small caps; keep the lowercase numerals of the English edition
        texbody = re.sub(r'\\roman\{(enum[iv]+)\}', r'\\romannumeral\\value{\1}', texbody)
    texbody, nrefs = re.subn(r'(\\subsection\{' + L['refs'] + r'\}\\label\{[^}]+\})',
                             lambda m: m.group(1) + '\n' + r'\begingroup\small\sloppy', texbody)
    assert nrefs == 1, 'references heading not found'
    texbody += '\n' + r'\endgroup' + '\n'

    preamble = (base/f'03_reproducibility/layout/series_{lang}.tex').read_text(encoding='utf-8')
    preamble += '\n' + r'\clubpenalty=10000\widowpenalty=10000\displaywidowpenalty=10000' + '\n'
    preamble += r'\usepackage{tikz}' + '\n'
    if lang == 'es':
        preamble += r'\tolerance=1500\emergencystretch=4em' + '\n'
    preamble += r'\AtBeginEnvironment{longtable}{\Needspace{16\baselineskip}}' + '\n'
    meta = (r'\hypersetup{pdftitle={' + title + r'},pdfauthor={Juan Pablo Traverso Gianini},pdflang={' + L['babel'] + '}'
            + r',colorlinks=true,linkcolor=blue,urlcolor=blue,citecolor=blue}' + '\n'
            + r'\title{' + title + '}\n'
            + r'\author{Juan Pablo Traverso Gianini\\\small ' + L['affil'] + r'\\\small '
              r'\href{mailto:jtraverso@gmail.com}{jtraverso@gmail.com}\\\small '
              r'\href{https://orcid.org/0009-0003-6068-4096}{ORCID: 0009-0003-6068-4096}}' + '\n'
            + r'\date{}\begin{document}\raggedbottom\maketitle' + '\n'
            + r'\begin{center}' + '\n' + front + '\n' + r'\end{center}' + '\n\n')
    tex = source.with_suffix('.tex')
    tex.write_bytes((preamble + meta + texbody + '\n\\end{document}\n').encode('utf-8'))
    passes = []
    for attempt in [1, 2]:
        run = subprocess.run([tectonic, '--keep-logs', tex.name], cwd=man, capture_output=True,
                             text=True, encoding='utf-8', errors='replace', env=fontenv)
        log = logs/f'{tex.stem}_{stamp}_pass{attempt}.log'
        log.write_text(run.stdout + '\n' + run.stderr, encoding='utf-8')
        assert run.returncode == 0, log
        passes.append({'path': log.relative_to(base).as_posix(), 'sha256': sha(log)})
    pdf = tex.with_suffix('.pdf')
    assert pdf.is_file()
    final_log = logs/f'{tex.stem}_{stamp}.log'
    shutil.move(str(tex.with_suffix('.log')), final_log)
    text = final_log.read_text(encoding='utf-8', errors='replace')
    assert 'Output written on ' + tex.stem in text, final_log
    return {'language': lang, 'source': source.relative_to(base).as_posix(), 'source_sha256': sha(source),
            'tex': tex.relative_to(base).as_posix(), 'tex_sha256': sha(tex),
            'pdf': pdf.relative_to(base).as_posix(), 'pdf_sha256': sha(pdf),
            'passes': passes, 'final_log': final_log.relative_to(base).as_posix(),
            'final_log_sha256': sha(final_log),
            'overfull_boxes': text.count('Overfull'),
            'undefined_references': len(re.findall(r'LaTeX Warning: (?:Reference|Citation) .*? undefined', text))
                                    + text.count('There were undefined references'),
            'font_warnings': text.count('LaTeX Font Warning'),
            'missing_characters': text.count('Missing character')}


langs = [a for a in sys.argv[1:] if a in LANG] or [l for l in LANG if (man/f'color_stats_{l}.md').exists()]
out = base/'02_validation/TYPESETTING.json'
old = json.loads(out.read_text(encoding='utf-8')) if out.exists() else {'documents': []}
docs = {d.get('language', 'en'): d for d in old.get('documents', [])}
for lang in langs:
    docs[lang] = build(lang)
    print('Built', Path(docs[lang]['pdf']).name, 'overfull', docs[lang]['overfull_boxes'],
          'missing', docs[lang]['missing_characters'], flush=True)
out.write_text(json.dumps({'status': 'PASS_COMPILATION', 'run': stamp,
                           'documents': [docs[l] for l in LANG if l in docs]}, indent=2) + '\n',
               encoding='utf-8', newline='\n')

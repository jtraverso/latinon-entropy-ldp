"""Typeset the GHHSBRIDGE note (EN and ES) through the series layout.

The Markdown files in 01_manuscript are the semantic sources. The layout files in
03_reproducibility/layout are copied unchanged from Latinon preprint 1.0. Pandoc
converts the body only; the title block and preamble come from the series layout.
Each PDF is compiled twice with Tectonic. Logs go to 02_validation/typesetting.
"""
from pathlib import Path
import subprocess, re, shutil, hashlib, datetime, json, os

base = Path(__file__).resolve().parents[1]
man = base/'01_manuscript'
logs = base/'02_validation/typesetting'
logs.mkdir(parents=True, exist_ok=True)
pandoc = shutil.which('pandoc') or str(Path.home()/'.cache/nw-typesetting/pandoc/pandoc-3.12.1/pandoc.exe')
tectonic = shutil.which('tectonic') or str(Path.home()/'.cache/nw-typesetting/tectonic/tectonic.exe')
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()

tmp = Path(os.environ.get('TEMP', str(Path.home())))/'ghhsbridge_typeset'
tmp.mkdir(exist_ok=True)
fontenv = os.environ.copy()
fontconfig = tmp/'fontconfig.xml'
fontconfig.write_text('<?xml version="1.0"?>\n<fontconfig><dir>C:/Windows/Fonts</dir><cachedir>'
                      + str(tmp/'fontcache').replace('\\', '/') + '</cachedir></fontconfig>\n', encoding='utf-8')
fontenv['FONTCONFIG_FILE'] = str(fontconfig)

LABELS = {
    'en': dict(date=r'\textbf{Preprint 1.0 --- 16 November 2026.}', repo='Repository',
               heads='Theorem|Lemma|Corollary|Proposition', refs='References'),
    'es': dict(date=r'\textbf{Preprint 1.0 --- 16 de noviembre de 2026.}', repo='Repositorio',
               heads='Teorema|Lema|Corolario|Proposición', refs='Referencias'),
}
# The DOI line is printed only when a reservation is recorded, and must agree with the Markdown.
reservation = base/'02_validation/ZENODO_RESERVATION.json'
doi = json.loads(reservation.read_text(encoding='utf-8'))['doi'] if reservation.is_file() else None
doi_line = (r'\textbf{DOI:} \href{https://doi.org/' + doi + '}{' + doi + '}.' + '\n\n') if doi else ''
stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
records = []
for lang in ['en', 'es']:
    lab = LABELS[lang]
    source = man/f'ghhsbridge_{lang}.md'
    md = source.read_text(encoding='utf-8')
    assert '\t' not in md and '\b' not in md
    assert (('DOI: https://doi.org/' + doi + '.') in md) if doi else ('\nDOI:' not in md), 'DOI line and reservation disagree'
    title = md.splitlines()[0].removeprefix('# ')
    body = md[md.index('## '):]
    conv = subprocess.run([pandoc, '--from=markdown+tex_math_dollars', '--to=latex', '--wrap=none'],
                          input=body, text=True, encoding='utf-8', capture_output=True, check=True)
    texbody = conv.stdout

    def inline_code(match):
        value = match.group(1)
        if ' ' in value:
            return r'\texttt{' + value + '}'
        plain = value.replace(r'\_', '_').replace(r'\textquotesingle{}', "'")
        # Short identifiers stay unbroken; long paths and hashes remain breakable.
        if len(plain) <= 30 and '/' not in plain:
            return r'\mbox{\path{' + plain + '}}'
        return r'\path{' + plain + '}'

    texbody = re.sub(r'\\texttt\{((?:[^{}]|\\textquotesingle\{\})+)\}', inline_code, texbody)
    texbody = re.sub(r'\\textbf\{((?:' + lab['heads'] + r') [^{}]+)\}',
                     lambda m: r'\Needspace{7\baselineskip}\textbf{' + m.group(1) + '}', texbody)
    texbody = texbody.replace('\n\\[', '\n\\nopagebreak[4]\n\\[')
    # The end-of-proof square never starts a line on its own.
    texbody = texbody.replace(r' \(\square\)', r'~\(\square\)')
    texbody = re.sub(r'(\\subsection\{' + lab['refs'] + r'\}\\label\{[^}]+\})',
                     lambda m: m.group(1) + '\n' + r'\begingroup\small', texbody)
    texbody += '\n' + r'\endgroup' + '\n'

    preamble = (base/f'03_reproducibility/layout/series_{lang}.tex').read_text(encoding='utf-8')
    preamble += '\n' + r'\clubpenalty=10000\widowpenalty=10000\displaywidowpenalty=10000' + '\n'
    meta = (r'\hypersetup{pdftitle={' + title + r'},pdfauthor={Juan Pablo Traverso Gianini},pdflang={' + lang
            + r'},colorlinks=true,linkcolor=blue,urlcolor=blue,citecolor=blue}' + '\n'
            + r'\title{' + title + '}\n'
            + r'\author{Juan Pablo Traverso Gianini\\\small Independent researcher, Santiago, Chile\\\small '
              r'\href{mailto:jtraverso@gmail.com}{jtraverso@gmail.com}\\\small '
              r'\href{https://orcid.org/0009-0003-6068-4096}{ORCID: 0009-0003-6068-4096}}' + '\n'
            + r'\date{}\begin{document}\raggedbottom\maketitle' + '\n'
            + lab['date'] + '\n\n' + doi_line
            + r'\textbf{' + lab['repo'] + r':} \url{https://github.com/jtraverso/latinon-entropy-ldp}.' + '\n\n')
    tex = source.with_suffix('.tex')
    tex.write_text(preamble + meta + texbody + '\n\\end{document}\n', encoding='utf-8')
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
    records.append({'source': source.relative_to(base).as_posix(), 'source_sha256': sha(source),
                    'tex': tex.relative_to(base).as_posix(), 'tex_sha256': sha(tex),
                    'pdf': pdf.relative_to(base).as_posix(), 'pdf_sha256': sha(pdf),
                    'passes': passes, 'final_log': final_log.relative_to(base).as_posix(),
                    'final_log_sha256': sha(final_log),
                    'overfull_boxes': text.count('Overfull'),
                    'undefined_references': text.count('undefined')})
    print('Built', pdf.name, flush=True)
(base/'02_validation/TYPESETTING.json').write_text(
    json.dumps({'status': 'PASS_COMPILATION', 'run': stamp, 'documents': records}, indent=2) + '\n',
    encoding='utf-8')

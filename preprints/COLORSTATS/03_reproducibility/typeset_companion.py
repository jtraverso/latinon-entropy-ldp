"""Typeset the formal companion (EN and ES) with the series layout; same pipeline as typeset_paper.py.

Sources: 05_formalization/formal_companion_{en,es}.md. Output TeX/PDF beside them; record in
05_formalization/TYPESETTING_COMPANION.json. Usage: python -I typeset_companion.py [en] [es]
"""
from pathlib import Path
import subprocess, re, shutil, hashlib, datetime, json, os, sys

base = Path(__file__).resolve().parents[1]
FORM = base/'05_formalization'
logs = FORM/'typesetting'
logs.mkdir(parents=True, exist_ok=True)
pandoc = shutil.which('pandoc') or str(Path.home()/'.cache/nw-typesetting/pandoc/pandoc-3.12.1/pandoc.exe')
tectonic = shutil.which('tectonic') or str(Path.home()/'.cache/nw-typesetting/tectonic/tectonic.exe')
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
tmp = Path(os.environ.get('TEMP', str(Path.home())))/'colorstats_typeset'
tmp.mkdir(exist_ok=True)
fontenv = os.environ.copy()
fontconfig = tmp/'fontconfig.xml'
fontconfig.write_text('<?xml version="1.0"?>\n<fontconfig><dir>C:/Windows/Fonts</dir><cachedir>'
                      + str(tmp/'fontcache').replace('\\', '/') + '</cachedir></fontconfig>\n', encoding='utf-8')
fontenv['FONTCONFIG_FILE'] = str(fontconfig)
AFFIL = {'en': 'Independent researcher, Santiago, Chile', 'es': 'Investigador independiente, Santiago, Chile'}
stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')


def front_block(lines):
    out = []
    for line in lines:
        line = line.strip()
        if not line or line == '---':
            continue
        m = re.match(r'^(.*?)(https?://\S+?)(\.?)$', line)
        out.append(m.group(1) + r'\url{' + m.group(2) + '}' + m.group(3) if m
                   else r'\textbf{' + line.replace('—', '---') + '}')
    return '\\\\\n'.join(out)


def inline_code(match):
    value = match.group(1)
    if ' ' in value or any(ord(c) > 127 for c in value):
        return r'\texttt{' + value + '}'
    plain = value.replace(r'\_', '_').replace(r'\textquotesingle{}', "'")
    return r'\path{' + plain + '}'


def build(lang):
    src = FORM/f'formal_companion_{lang}.md'
    md = src.read_text(encoding='utf-8')
    title = md.splitlines()[0].removeprefix('# ')
    head = md[:md.index('\n## ')].splitlines()
    front = front_block(head[3:])
    body = md[md.index('\n## ') + 1:]
    tex_body = subprocess.run([pandoc, '--from=markdown+tex_math_dollars', '--to=latex', '--wrap=none'],
                              input=body, text=True, encoding='utf-8', capture_output=True, check=True).stdout
    tex_body = re.sub(r'\\texttt\{((?:[^{}]|\\textquotesingle\{\})+)\}', inline_code, tex_body)
    pre = (base/f'03_reproducibility/layout/series_{lang}.tex').read_text(encoding='utf-8')
    # Lean identifiers contain Greek letters, subscripts and relation symbols that Latin Modern Mono lacks
    pre = pre.replace(r'\setmonofont{lmmono10-regular.otf}[Scale=MatchLowercase]',
                      r'\setmonofont{Consolas}[Scale=MatchLowercase]')
    pre += '\n' + r'\clubpenalty=10000\widowpenalty=10000\sloppy' + '\n' + r'\usepackage{newunicodechar}' + '\n'
    for ch, cmd in [('∈', r'\in'), ('∌', r'\not\ni'), ('∣', r'\mid'), ('∨', r'\vee'), ('⊂', r'\subset'),
                    ('⊗', r'\otimes'), ('⊠', r'\boxtimes'), ('⌈', r'\lceil'), ('⌉', r'\rceil'), ('𝒯', r'\mathcal{T}'),
                    ('⇐', r'\Leftarrow'), ('ℤ', r'\mathbb{Z}'), ('⁺', r'^{+}'), ('′', r'^{\prime}')]:
        pre += r'\newunicodechar{' + ch + r'}{\ensuremath{' + cmd + '}}' + '\n'
    meta = (r'\hypersetup{pdftitle={' + title + r'},pdfauthor={Juan Pablo Traverso Gianini},pdflang={' + lang + '}'
            + r',colorlinks=true,linkcolor=blue,urlcolor=blue}' + '\n' + r'\title{' + title + '}\n'
            + r'\author{Juan Pablo Traverso Gianini\\\small ' + AFFIL[lang] + r'\\\small '
              r'\href{https://orcid.org/0009-0003-6068-4096}{ORCID: 0009-0003-6068-4096}}' + '\n'
            + r'\date{}\begin{document}\raggedbottom\maketitle' + '\n'
            + r'\begin{center}' + '\n' + front + '\n' + r'\end{center}' + '\n\n')
    tex = src.with_suffix('.tex')
    tex.write_bytes((pre + meta + tex_body + '\n\\end{document}\n').encode('utf-8'))
    for attempt in (1, 2):
        run = subprocess.run([tectonic, '--keep-logs', tex.name], cwd=FORM, capture_output=True, text=True,
                             encoding='utf-8', errors='replace', env=fontenv)
        (logs/f'{tex.stem}_{stamp}_pass{attempt}.log').write_text(run.stdout + '\n' + run.stderr, encoding='utf-8')
        assert run.returncode == 0, attempt
    final = logs/f'{tex.stem}_{stamp}.log'
    shutil.move(str(tex.with_suffix('.log')), final)
    text = final.read_text(encoding='utf-8', errors='replace')
    for junk in (tex.with_suffix('.aux'), tex.with_suffix('.out')):
        if junk.exists():
            junk.unlink()
    return {'language': lang, 'source': src.name, 'source_sha256': sha(src), 'tex': tex.name, 'tex_sha256': sha(tex),
            'pdf': tex.with_suffix('.pdf').name, 'pdf_sha256': sha(tex.with_suffix('.pdf')),
            'final_log': final.relative_to(FORM).as_posix(), 'final_log_sha256': sha(final),
            'overfull_boxes': text.count('Overfull'), 'missing_characters': text.count('Missing character'),
            'undefined_references': len(re.findall(r'LaTeX Warning: (?:Reference|Citation) .*? undefined', text))}


langs = [a for a in sys.argv[1:] if a in AFFIL] or [l for l in AFFIL if (FORM/f'formal_companion_{l}.md').exists()]
out = FORM/'TYPESETTING_COMPANION.json'
docs = {d['language']: d for d in (json.loads(out.read_text(encoding='utf-8'))['documents'] if out.exists() else [])}
for l in langs:
    docs[l] = build(l)
    print('Built', docs[l]['pdf'], 'overfull', docs[l]['overfull_boxes'], 'missing', docs[l]['missing_characters'])
out.write_bytes((json.dumps({'status': 'PASS_COMPILATION', 'run': stamp,
                             'documents': [docs[l] for l in AFFIL if l in docs]}, indent=2) + '\n').encode('utf-8'))

"""Bilingual parity and PDF checks for the GHHSBRIDGE note. Run after typesetting.

Compares the EN and ES Markdown sources (headings, numbered results, equation tags,
display formulas, code identifiers, tables, references), checks the text layer and the
hyperlinks of both PDFs, and renders every page. Writes 02_validation/DOCUMENT_AUDIT.json.
"""
from pathlib import Path
import re, json, hashlib, sys
import pymupdf

base = Path(__file__).resolve().parents[1]
man = base/'01_manuscript'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
problems = []


def facts(md):
    display = re.findall(r'\$\$\n(.*?)\n\$\$', md, re.S)
    return {
        'sections': len(re.findall(r'^## ', md, re.M)),
        'section_numbers': re.findall(r'^## (\d+)\.', md, re.M),
        'results': re.findall(r'^\*\*(?:Theorem|Lemma|Teorema|Lema) (\d+\.\d+)', md, re.M),
        'proofs': len(re.findall(r'^\*(?:Proof|Demostración)\.\*', md, re.M)),
        'qed': md.count(r'$\square$'),
        'tags': re.findall(r'\\tag\{([^}]+)\}', md),
        'display': display,
        'code': sorted(set(re.findall(r'`([^`\n]+)`', md))),
        'table_rows': len(re.findall(r'^\| ', md, re.M)),
        'references': re.findall(r'^\[(\d+)\] ', md, re.M),
        # A citation is [n] or [n, locator]; the interval [0,1] has no space after the comma.
        'citations': sorted(set(re.findall(r'\[(\d)(?:, |\])', md))),
        'code_blocks': re.findall(r'^```\n(.*?)\n```', md, re.S | re.M),
    }


src = {lang: (man/f'ghhsbridge_{lang}.md').read_text(encoding='utf-8') for lang in ['en', 'es']}
f = {lang: facts(src[lang]) for lang in src}
for key in f['en']:
    if f['en'][key] != f['es'][key]:
        problems.append(f'bilingual mismatch: {key}')
if f['en']['proofs'] != f['en']['qed']:
    problems.append('proof/qed count')
if sorted(f['en']['references']) != sorted(c for c in f['en']['citations']):
    problems.append('references not all cited or cited without entry')

# Identifiers named in the note must exist in the frozen sources.
freeze = json.loads((base/'02_validation/FREEZE.json').read_text(encoding='utf-8'))
import zipfile
with zipfile.ZipFile(base/freeze['source_archive']['path']) as z:
    lean_text = '\n'.join(z.read(n).decode('utf-8') for n in z.namelist() if n.endswith('.lean'))
skip = {'sorry', 'propext', 'Classical.choice', 'Quot.sound', 'lake build GHHSBridge', 'GHHSBridge',
        'Latinon_Lean_v1.0.zip', 'ReviewAxioms.lean', 'GHHSBridge_Lean_v1.0', 'Latinon_Lean_v1.0',
        'GHHSBridge_Lean_v1.0/lean', freeze['mathlib_commit'],
        'preprints/GHHSBRIDGE/05_formalization/GHHSBridge_Lean_v1.0.zip', 'preprints/GHHSBRIDGE/02_validation',
        'preprints/GHHSBRIDGE'}
identifiers = [c for c in f['en']['code'] if c not in skip]
missing = []
for ident in identifiers:
    last = ident.split('.')[-1]
    if not re.search(r'(?:theorem|def|structure|lemma|instance) (?:\w+\.)?' + re.escape(last) + r"(?![\w'])", lean_text) \
            and not re.search(r'^import GHHSBridge\.' + re.escape(ident) + r'$', lean_text, re.M):
        missing.append(ident)
if missing:
    problems.append('identifiers not found in sources: ' + ', '.join(missing))

pdfs = {}
renders = base.parent.parent/'tmp_renders'
for lang in ['en', 'es']:
    pdf = man/f'ghhsbridge_{lang}.pdf'
    doc = pymupdf.open(pdf)
    text = '\n'.join(p.get_text() for p in doc)
    joined = re.sub(r'\s+', ' ', text)
    absent = [c for c in identifiers if c not in joined and c.replace(' ', '') not in joined.replace(' ', '')]
    spaced = [c for c in identifiers if c not in joined]
    links = sorted({l['uri'] for p in doc for l in p.get_links() if l.get('uri')})
    out = renders/lang
    out.mkdir(parents=True, exist_ok=True)
    for i, p in enumerate(doc):
        p.get_pixmap(dpi=110).save(str(out/f'p{i+1}.png'))
    for tag in f[lang]['tags']:
        if f'({tag})' not in joined:
            problems.append(f'{lang}: equation tag ({tag}) not in PDF text')
    if absent:
        problems.append(f'{lang}: identifiers missing from PDF text: {absent}')
    pdfs[lang] = {'pdf': pdf.relative_to(base).as_posix(), 'sha256': sha(pdf), 'pages': len(doc),
                  'identifiers_split_by_layout': spaced, 'links': links,
                  'rendered_pages': len(doc), 'render_dpi': 110}

report = {
    'status': 'PASS' if not problems else 'FAIL', 'problems': problems,
    'sources': {lang: {'path': f'01_manuscript/ghhsbridge_{lang}.md', 'sha256': sha(man/f'ghhsbridge_{lang}.md')}
                for lang in src},
    'parity': {k: (len(v) if isinstance(v, list) else v) for k, v in f['en'].items()},
    'numbered_results': f['en']['results'], 'equation_tags': f['en']['tags'],
    'identifiers_checked_against_sources': identifiers, 'pdf': pdfs,
}
(base/'02_validation/DOCUMENT_AUDIT.json').write_text(json.dumps(report, indent=2, ensure_ascii=False) + '\n',
                                                     encoding='utf-8', newline='\n')
print(report['status'], problems)
print({k: v['pages'] for k, v in pdfs.items()}, pdfs['en']['links'])
print('split:', pdfs['en']['identifiers_split_by_layout'], pdfs['es']['identifiers_split_by_layout'])

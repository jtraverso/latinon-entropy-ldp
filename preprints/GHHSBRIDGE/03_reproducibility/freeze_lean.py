"""Package the frozen Lean sources and record the freeze evidence.

Usage:
  python freeze_lean.py <frozen lean directory> <Latinon_Lean_v1.0.zip> <Latinon tree used for the build>

Writes 05_formalization/GHHSBridge_Lean_v1.0.zip (sources only, fixed timestamps) and
02_validation/FREEZE.json. It does not run Lean; the build log and the axiom output in
02_validation/lean were produced by the two commands in the README.
"""
from pathlib import Path
import sys, json, hashlib, zipfile, re

base = Path(__file__).resolve().parents[1]
lean = Path(sys.argv[1]).resolve()
latinon_zip = Path(sys.argv[2]).resolve()
latinon_tree = Path(sys.argv[3]).resolve()
sha_bytes = lambda b: hashlib.sha256(b).hexdigest()
sha = lambda p: sha_bytes(p.read_bytes())

# 1. Source list (no build products).
files = sorted(p for p in lean.rglob('*') if p.is_file() and '.lake' not in p.parts
               and p.name != 'source_manifest.json')
manifest = {p.relative_to(lean).as_posix(): sha(p) for p in files}
(lean/'source_manifest.json').write_text(json.dumps(manifest, indent=2) + '\n', encoding='utf-8', newline='\n')
files.append(lean/'source_manifest.json')

# 2. Static checks on the sources.
lean_files = [p for p in files if p.suffix == '.lean']
modules = sorted(p for p in lean_files if p.parent.name == 'GHHSBridge')
root_imports = re.findall(r'^import (GHHSBridge\.\w+)$', (lean/'GHHSBridge.lean').read_text(encoding='utf-8'), re.M)
assert sorted(root_imports) == sorted('GHHSBridge.' + p.stem for p in modules), root_imports
escape = {}
for p in lean_files:
    text = p.read_text(encoding='utf-8')
    escape[p.relative_to(lean).as_posix()] = {
        'sorry': len(re.findall(r'\bsorry\b', text)),
        'axiom_declarations': len(re.findall(r'^\s*axiom\s', text, re.M)),
        'native_decide': text.count('native_decide'),
        'implemented_by': text.count('implemented_by'),
        'unsafe': len(re.findall(r'^\s*unsafe\s', text, re.M)),
        'lines': text.count('\n'),
    }
assert all(v['sorry'] == 0 and v['axiom_declarations'] == 0 and v['native_decide'] == 0
           and v['implemented_by'] == 0 and v['unsafe'] == 0 for v in escape.values()), escape

# 3. Source archive with fixed timestamps.
out = base/'05_formalization/GHHSBridge_Lean_v1.0.zip'
with zipfile.ZipFile(out, 'w', zipfile.ZIP_DEFLATED) as z:
    for p in files:
        info = zipfile.ZipInfo('lean/' + p.relative_to(lean).as_posix(), date_time=(2026, 11, 16, 0, 0, 0))
        info.compress_type = zipfile.ZIP_DEFLATED
        info.external_attr = 0o644 << 16
        z.writestr(info, p.read_bytes())

# 4. Dependency identity: the Latinon tree used for the build against the released archive.
same, differing, missing = 0, [], []
with zipfile.ZipFile(latinon_zip) as z:
    names = [n for n in z.namelist() if not n.endswith('/')]
    for n in names:
        rel = n.split('/', 1)[1]
        q = latinon_tree/rel
        if not q.is_file():
            missing.append(n); continue
        a, b = z.read(n), q.read_bytes()
        if a == b or a.replace(b'\r\n', b'\n') == b.replace(b'\r\n', b'\n'):
            same += 1
        else:
            differing.append(n)
assert not missing and differing == ['lean/source_manifest.json'], (missing, differing)

# 5. Recorded Lean evidence.
build_log = base/'02_validation/lean/build_GHHSBridge.log'
axiom_log = base/'02_validation/lean/review_axioms.log'
blog = build_log.read_text(encoding='utf-8', errors='replace')
alog = axiom_log.read_text(encoding='utf-8', errors='replace')
built = re.findall(r'Built (GHHSBridge(?:\.\w+)?) ', blog)
assert sorted(built) == sorted(['GHHSBridge'] + ['GHHSBridge.' + p.stem for p in modules]), built
assert 'Build completed successfully' in blog and blog.rstrip().endswith('exit=0')
other_built = [m for m in re.findall(r'Built (\S+) ', blog) if not m.startswith('GHHSBridge')]
queries = re.findall(r"^'(GHHSBridge\.[^']*(?:')?)' depends on axioms: \[(.*)\]$", alog, re.M)
axioms = sorted({a.strip() for _, lst in queries for a in lst.split(',')})
assert len(queries) == 12 and axioms == ['Classical.choice', 'Quot.sound', 'propext'], (len(queries), axioms)
assert alog.rstrip().endswith('exit=0')
jobs = re.search(r'Build completed successfully \((\d+) jobs\)', blog).group(1)

freeze = {
    'paper_id': 'GHHSBRIDGE', 'edition': '1.0', 'date': '2026-11-16',
    'lean_toolchain': (lean/'lean-toolchain').read_text(encoding='utf-8').strip(),
    'mathlib_commit': '56a005855ea17e0b0958f73ec801ae140b0a1679',
    'source_archive': {'path': out.relative_to(base).as_posix(), 'sha256': sha(out), 'files': len(files)},
    'modules': [p.stem for p in modules],
    'module_lines_total': sum(escape['GHHSBridge/' + p.name]['lines'] for p in modules),
    'root': {'file': 'GHHSBridge.lean', 'imports': root_imports},
    'static_checks': escape,
    'dependency': {
        'archive': latinon_zip.name, 'sha256': sha(latinon_zip),
        'files_compared': len(names), 'identical': same, 'differing': differing,
        'note': 'The differing file is a generated manifest. The tree used for the build was not rebuilt in this run.'},
    'build': {'command': 'lake build GHHSBridge', 'log': build_log.relative_to(base).as_posix(),
              'log_sha256': sha(build_log), 'jobs': int(jobs), 'targets_compiled_in_this_run': built,
              'dependency_targets_compiled_in_this_run': other_built,
              'note': 'All other jobs were replayed from existing compiled objects of the Latinon sources and Mathlib.'},
    'axioms': {'command': 'lake env lean ReviewAxioms.lean', 'log': axiom_log.relative_to(base).as_posix(),
               'log_sha256': sha(axiom_log), 'queries': [q for q, _ in queries], 'axioms_reported': axioms},
}
(base/'02_validation/FREEZE.json').write_text(json.dumps(freeze, indent=2) + '\n', encoding='utf-8', newline='\n')
print('archive', sha(out)); print('modules', len(modules), 'lines', freeze['module_lines_total'], 'jobs', jobs)

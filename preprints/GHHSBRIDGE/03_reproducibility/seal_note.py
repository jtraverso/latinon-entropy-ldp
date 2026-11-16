"""Seal the GHHSBRIDGE package. Run last.

Checks that the recorded evidence refers to the current files, writes
04_integrity/MANIFEST.json (SHA-256 of every packaged file except itself), then the
package archive and its checksum sidecar in <working project>/archives.
"""
from pathlib import Path
import json, hashlib, zipfile

base = Path(__file__).resolve().parents[1]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
load = lambda rel: json.loads((base/rel).read_text(encoding='utf-8'))

# 1. Evidence must be bound to the current bytes.
ts = load('02_validation/TYPESETTING.json')
for d in ts['documents']:
    for key in ['source', 'tex', 'pdf', 'final_log']:
        assert sha(base/d[key]) == d[key + '_sha256'], (key, d[key])
    assert d['overfull_boxes'] == 0 and d['undefined_references'] == 0
audit = load('02_validation/DOCUMENT_AUDIT.json')
assert audit['status'] == 'PASS'
for lang, rec in audit['pdf'].items():
    assert sha(base/rec['pdf']) == rec['sha256'], lang
for lang, rec in audit['sources'].items():
    assert sha(base/rec['path']) == rec['sha256'], lang
fr = load('02_validation/FREEZE.json')
assert sha(base/fr['source_archive']['path']) == fr['source_archive']['sha256']
assert sha(base/fr['build']['log']) == fr['build']['log_sha256']
assert sha(base/fr['axioms']['log']) == fr['axioms']['log_sha256']
with zipfile.ZipFile(base/fr['source_archive']['path']) as z:
    inner = json.loads(z.read('lean/source_manifest.json'))
    for name, digest in inner.items():
        assert hashlib.sha256(z.read('lean/' + name)).hexdigest() == digest, name

# 2. Manifest.
manifest_path = base/'04_integrity/MANIFEST.json'
files = sorted(p for p in base.rglob('*') if p.is_file() and p != manifest_path)
manifest = {p.relative_to(base).as_posix(): sha(p) for p in files}
manifest_path.write_text(json.dumps(manifest, indent=1) + '\n', encoding='utf-8', newline='\n')

# 3. Archive and sidecar (last mutation).
archives = base.parents[1]/'archives'
archives.mkdir(exist_ok=True)
archive = archives/'GHHSBridge_preprint_v1.0.zip'
with zipfile.ZipFile(archive, 'w', zipfile.ZIP_DEFLATED) as z:
    for p in sorted(files + [manifest_path]):
        info = zipfile.ZipInfo('preprints/GHHSBRIDGE/' + p.relative_to(base).as_posix(),
                               date_time=(2026, 11, 16, 0, 0, 0))
        info.compress_type = zipfile.ZIP_DEFLATED
        info.external_attr = 0o644 << 16
        z.writestr(info, p.read_bytes())
(archives/(archive.name + '.sha256')).write_text(sha(archive) + '  ' + archive.name + '\n',
                                                 encoding='utf-8', newline='\n')
print('files', len(files) + 1); print('manifest', sha(manifest_path)); print('archive', sha(archive))

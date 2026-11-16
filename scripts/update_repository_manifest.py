"""Regenerate the root manifest_sha256.txt after a catalogue change.

Uses the file selection of seal_preprint.py (no .git, .lake, tmp, __pycache__ or
archives; no build by-products; the archive index and the manifest itself excluded).
It writes only manifest_sha256.txt and changes no paper file or sealed archive.
"""
from pathlib import Path
import hashlib,os

ROOT=Path(__file__).resolve().parents[1]

def files():
    for parent,dirs,names in os.walk(ROOT):
        dirs[:]=[d for d in dirs if d not in ['.git','.lake','tmp','__pycache__','archives']]
        for name in names:
            p=Path(parent)/name;rel=p.relative_to(ROOT)
            if p.suffix in ['.aux','.out','.olean','.ilean'] or '.olean.' in name:continue
            if rel.as_posix() in ['publication/PACKAGE_ARCHIVE.json','manifest_sha256.txt']:continue
            yield rel

if __name__=='__main__':
    selected={p.as_posix():hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(files())}
    (ROOT/'manifest_sha256.txt').write_text(''.join(h+'  '+n+'\n' for n,h in selected.items()),
        encoding='utf-8',newline='\n')
    print(len(selected),'files')

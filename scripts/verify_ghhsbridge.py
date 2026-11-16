"""Read-only verification of the GHHSBRIDGE research note, preprint 1.0; no network, no Lean.

Checks the package manifest, the bindings between Markdown, TeX, PDF and logs, the
document audit, the Lean freeze record (source archive, build log, axiom output,
static source checks), the Zenodo reservation, the catalogue entry and the complete
package archive with its sidecar.
"""
from pathlib import Path
import hashlib,json,re,zipfile

ROOT=Path(__file__).resolve().parents[1]
B=Path('preprints/GHHSBRIDGE')
ARCHIVE=Path('archives/GHHSBridge_preprint_v1.0.zip')
STANDARD=['Classical.choice','Quot.sound','propext']

def digest(p):return hashlib.sha256((ROOT/p).read_bytes()).hexdigest()
def read(p):return json.loads((ROOT/p).read_text(encoding='utf-8'))

def check():
    # Package manifest: every file listed, nothing extra.
    manifest=read(B/'04_integrity/MANIFEST.json')
    present={p.relative_to(ROOT/B).as_posix() for p in (ROOT/B).rglob('*') if p.is_file()}
    assert present-{'04_integrity/MANIFEST.json'}==set(manifest),sorted(present^set(manifest))
    for name,h in manifest.items():assert digest(B/name)==h,name
    # Markdown -> TeX -> PDF -> logs.
    ts=read(B/'02_validation/TYPESETTING.json')
    assert ts['status']=='PASS_COMPILATION' and len(ts['documents'])==2
    for d in ts['documents']:
        for key in ['source','tex','pdf','final_log']:assert digest(B/d[key])==d[key+'_sha256'],d[key]
        for log in d['passes']:assert digest(B/log['path'])==log['sha256'],log['path']
        assert d['overfull_boxes']==0 and d['undefined_references']==0
    audit=read(B/'02_validation/DOCUMENT_AUDIT.json')
    assert audit['status']=='PASS' and audit['problems']==[]
    for rec in audit['pdf'].values():assert digest(B/rec['pdf'])==rec['sha256'],rec['pdf']
    for rec in audit['sources'].values():assert digest(B/rec['path'])==rec['sha256'],rec['path']
    # Lean freeze.
    fr=read(B/'02_validation/FREEZE.json')
    assert digest(B/fr['source_archive']['path'])==fr['source_archive']['sha256']
    assert digest(B/fr['build']['log'])==fr['build']['log_sha256']
    assert digest(B/fr['axioms']['log'])==fr['axioms']['log_sha256']
    blog=(ROOT/B/fr['build']['log']).read_text(encoding='utf-8',errors='replace')
    assert 'Build completed successfully' in blog and blog.rstrip().endswith('exit=0')
    alog=(ROOT/B/fr['axioms']['log']).read_text(encoding='utf-8',errors='replace')
    queries=re.findall(r"^'(GHHSBridge\.[^']*'?)' depends on axioms: \[(.*)\]$",alog,re.M)
    assert len(queries)==12 and alog.rstrip().endswith('exit=0')
    assert sorted({a.strip() for _,lst in queries for a in lst.split(',')})==STANDARD
    with zipfile.ZipFile(ROOT/B/fr['source_archive']['path']) as z:
        assert z.testzip() is None
        inner=json.loads(z.read('lean/source_manifest.json'))
        for name,h in inner.items():assert hashlib.sha256(z.read('lean/'+name)).hexdigest()==h,name
        lean_files=[n for n in z.namelist() if n.endswith('.lean')]
        for n in lean_files:
            text=z.read(n).decode('utf-8')
            assert not re.search(r'\bsorry\b',text),n
            assert not re.search(r'^\s*axiom\s',text,re.M),n
            assert 'native_decide' not in text and 'implemented_by' not in text,n
        root_imports=re.findall(r'^import (GHHSBridge\.\w+)$',z.read('lean/GHHSBridge.lean').decode('utf-8'),re.M)
    assert sorted(root_imports)==sorted('GHHSBridge.'+m for m in fr['modules']) and len(root_imports)==7
    # Reservation, manuscripts and catalogue.
    res=read(B/'02_validation/ZENODO_RESERVATION.json')
    assert res['status']=='RESERVED_NOT_PUBLISHED' and res['submitted'] is False
    doi=res['doi'];assert doi=='10.5281/zenodo.'+str(res['id'])
    for lang in ['en','es']:
        assert 'DOI: https://doi.org/'+doi+'.' in (ROOT/B/f'01_manuscript/ghhsbridge_{lang}.md').read_text(encoding='utf-8')
    index=read('PUBLICATION_INDEX.json')
    entry=[p for p in index['papers'] if p['id']=='GHHSBRIDGE']
    assert len(entry)==1 and entry[0]['doi']==doi and entry[0]['version']=='1.0'
    assert entry[0]['directory']==B.as_posix() and entry[0]['doi_status']=='reserved_not_published'
    # Complete package archive.
    sidecar=(ROOT/(ARCHIVE.as_posix()+'.sha256')).read_text(encoding='utf-8').strip()
    assert sidecar==digest(ARCHIVE)+'  '+ARCHIVE.name
    with zipfile.ZipFile(ROOT/ARCHIVE) as z:
        names=set(z.namelist());assert len(names)==len(z.namelist()) and z.testzip() is None
        assert names=={(B/n).as_posix() for n in present},sorted(names^{(B/n).as_posix() for n in present})
        for n in names:assert hashlib.sha256(z.read(n)).hexdigest()==digest(n),n
    return {'status':'PASS','paper':'GHHSBRIDGE','version':'1.0','doi':doi,
        'package_files':len(present),'documents':len(ts['documents']),
        'pdf_pages':{k:v['pages'] for k,v in audit['pdf'].items()},
        'lean_modules':len(root_imports),'axiom_queries':len(queries),'axioms':STANDARD,
        'archive_sha256':digest(ARCHIVE),
        'scope':'Read-only check of the delivered note, its recorded Lean evidence and package hashes; does not invoke Lean or constitute peer review'}

if __name__=='__main__':print(json.dumps(check(),indent=2))

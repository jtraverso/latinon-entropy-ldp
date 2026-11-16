"""Seal internally audited edition 1.0; does not publish or change visibility."""
from pathlib import Path
import datetime,hashlib,json,os,re,zipfile
from verify_repository import ROOT,P,V,read,digest,check_evidence,check_mathematics,check_documents,check_metadata

def put(name,data):
    path=ROOT/name;path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(data,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')

evidence=check_evidence();mathematics=check_mathematics();documents=check_documents()
assert read(V/'SEMANTIC_DIFF.json')['manuscripts']==mathematics
assert read(V/'RECONSTRUCTION_BINDING.json')['status']=='PASS_RETAINED_RECONSTRUCTION_BINDING'
assert read(V/'CDR_STRUCTURE_COMPARISON.json')['status']=='PASS_CDR_STRUCTURE_COMPARISON'
assert '**PASS_TARGETED_WRITTEN_REVIEW**' in (ROOT/'publication/audit/PRINTED_PROOFS.md').read_text(encoding='utf-8')
assert '**PASS_SCOPED_BIBLIOGRAPHIC_REVIEW**' in (ROOT/'publication/audit/LITERATURE_REVIEW.md').read_text(encoding='utf-8')
checks={name:'PASS' for name in ['retained_source_bound_reconstruction','source_only_lean_freeze',
    'eight_endpoint_and_three_good_rate_axiom_queries','protected_mathematical_content',
    'targeted_written_proof_review','scoped_bibliography_review','bilingual_parity',
    'source_tex_pdf_binding','all_rendered_pages','cdr_structure_and_layout','metadata_and_license']}
paths=[P/'02_validation/CLEAN_REBUILD_AUDIT.json',P/'02_validation/SOURCE_AUDIT.json',
    P/'02_validation/FINITE_REGRESSIONS.json',Path('publication/PROOF_LEDGER.json'),
    Path('publication/audit/PROTECTED_CONTRACT_AUDIT.json'),Path('publication/audit/SOURCE_SNAPSHOT.json'),
    Path('publication/audit/PRINTED_PROOFS.md'),Path('publication/audit/LITERATURE_REVIEW.md'),
    Path('publication/audit/EDITORIAL_REPORT.md')]
paths += [V/name for name in ['FREEZE.json','PROTECTED_BASELINE.json','SEMANTIC_DIFF.json',
    'RECONSTRUCTION_BINDING.json','PROVENANCE.json','CDR_STRUCTURE_COMPARISON.json',
    'TYPESETTING.json','DOCUMENT_AUDIT.json','VISUAL_REVIEW.json']]
report={'status':'PASS_INTERNAL_RELEASE_AUDIT','editorial_verdict':'EDITORIALLY_READY',
    'version':'1.0','completed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'scope':'Internal edition preparation, source binding, semantic and rendered-artifact checks; not independent peer review or public-access certification',
    **evidence,**documents,'checks':checks,'mathematical_sources_changed':False,
    'cdr_standard_commit':'d12d980f8c86d8795e9faa0c6bb274ee936c7c8e',
    'evidence':{p.as_posix():digest(p) for p in paths},
    'limitations':['Pinned external Mathlib ecosystem caches reused, not rebuilt',
        'Targeted internal written review, not independent review of all analytic providers',
        'Scoped literature search, not exhaustive priority certification',
        'CDR application assumes a completed base and counts a fixed-residue family']}
put('publication/LATINON_RELEASE_AUDIT.json',report);put(V/'AUDIT_RESULT.json',report)
put('publication/RELEASE_CHECKS.json',{'status':'PASS','version':'1.0','documents':4,
    'release_audit':'publication/LATINON_RELEASE_AUDIT.json',
    'release_audit_sha256':digest('publication/LATINON_RELEASE_AUDIT.json'),
    'source_lean_freeze_unchanged':True,'visibility_is_an_operational_setting':True})
check_metadata()

def files():
    for parent,dirs,names in os.walk(ROOT):
        dirs[:]=[d for d in dirs if d not in ['.git','.lake','tmp','__pycache__','archives']]
        for name in names:
            p=Path(parent)/name;rel=p.relative_to(ROOT)
            if p.suffix in ['.aux','.out','.olean','.ilean'] or '.olean.' in name:continue
            if rel.as_posix() in ['publication/PACKAGE_ARCHIVE.json','manifest_sha256.txt']:continue
            yield rel

paper_manifest=P/'04_integrity/MANIFEST.json'
put(paper_manifest,{p.relative_to(P).as_posix():digest(p) for p in sorted(files())
    if p.is_relative_to(P) and p!=paper_manifest})
credential=re.compile(rb'gh[pousr]_[A-Za-z0-9]{25,}|github_pat_[A-Za-z0-9_]{30,}|-----BEGIN (?:RSA |OPENSSH )?PRIVATE KEY-----')
selected={p.as_posix():digest(p) for p in sorted(files())}
for name in selected:
    path=ROOT/name
    if path.suffix in ['.md','.tex','.py','.json','.txt','.yml','.cff']:
        assert not credential.search(path.read_bytes()),name
with zipfile.ZipFile(ROOT/read(V/'FREEZE.json')['archive']) as z:
    for name in z.namelist():assert not credential.search(z.read(name)),name
manifest=ROOT/'manifest_sha256.txt'
manifest.write_text(''.join(h+'  '+name+'\n' for name,h in selected.items()),encoding='utf-8',newline='\n')
selected['manifest_sha256.txt']=digest('manifest_sha256.txt')
archive=Path('archives/Latinon_preprint_v1.0.zip');(ROOT/archive).parent.mkdir(exist_ok=True)
with zipfile.ZipFile(ROOT/archive,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
    for name in sorted(selected):
        info=zipfile.ZipInfo(name,date_time=(2026,11,16,0,0,0))
        info.compress_type=zipfile.ZIP_DEFLATED;info.external_attr=0o100644<<16
        z.writestr(info,(ROOT/name).read_bytes(),compresslevel=9)
archive_hash=digest(archive)
(ROOT/(str(archive)+'.sha256')).write_text(archive_hash+'  '+archive.name+'\n',encoding='utf-8',newline='\n')
put('publication/PACKAGE_ARCHIVE.json',{'version':'1.0','archive':archive.as_posix(),
    'sha256':archive_hash,'bytes':(ROOT/archive).stat().st_size,'entry_sha256':selected,
    'scope':'Complete edition package; archive index and sidecar are external to avoid recursive hashing'})
print(json.dumps({'status':report['status'],'version':'1.0','packaged_files':len(selected),
    'rendered_pages':documents['rendered_pages'],'archive_sha256':archive_hash},indent=2))

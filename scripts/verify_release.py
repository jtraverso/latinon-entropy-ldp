"""Read-only verification of the complete LATINON archive and edition; no network.

The files of the Latinon paper and its audit (preprints/LATINON/, publication/) must
equal the entries of its sealed archive. Repository catalogue files (README, series
catalogue, index, citations, root manifest, scripts, CI) are checked inside the archive
and may grow with later papers; they are reported, not required to be unchanged. The
tag latinon-v1.0 keeps the edition exactly as released.
"""
from pathlib import Path
import hashlib,json,zipfile,sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
from verify_repository import ROOT,check,read,digest

LATINON_OWNED=('preprints/LATINON/','publication/')

if __name__=='__main__':
    result=check();record=read('publication/PACKAGE_ARCHIVE.json')
    assert record['version']=='1.0' and digest(record['archive'])==record['sha256']
    sidecar=(ROOT/(record['archive']+'.sha256')).read_text().strip()
    assert sidecar==record['sha256']+'  '+Path(record['archive']).name
    changed=[]
    with zipfile.ZipFile(ROOT/record['archive']) as z:
        assert len(z.namelist())==len(set(z.namelist()))
        assert set(z.namelist())==set(record['entry_sha256']) and z.testzip() is None
        for name,h in record['entry_sha256'].items():
            assert hashlib.sha256(z.read(name)).hexdigest()==h,name
            if name.startswith(LATINON_OWNED):
                assert digest(name)==h,name
            elif not (ROOT/name).is_file() or digest(name)!=h:
                changed.append(name)
    result.update(complete_archive='PASS',archive_sha256=record['sha256'],
        latinon_files_unchanged='PASS',
        repository_files_changed_since_edition=sorted(changed))
    print(json.dumps(result,indent=2))

"""Read-only verification of the complete archive and edition; no network."""
from pathlib import Path
import hashlib,json,zipfile
from verify_repository import ROOT,check,read,digest

if __name__=='__main__':
    result=check();record=read('publication/PACKAGE_ARCHIVE.json')
    assert record['version']=='1.0' and digest(record['archive'])==record['sha256']
    sidecar=(ROOT/(record['archive']+'.sha256')).read_text().strip()
    assert sidecar==record['sha256']+'  '+Path(record['archive']).name
    with zipfile.ZipFile(ROOT/record['archive']) as z:
        assert len(z.namelist())==len(set(z.namelist()))
        assert set(z.namelist())==set(record['entry_sha256']) and z.testzip() is None
        for name,h in record['entry_sha256'].items():
            assert hashlib.sha256(z.read(name)).hexdigest()==digest(name)==h,name
    result.update(complete_archive='PASS',archive_sha256=record['sha256'])
    print(json.dumps(result,indent=2))

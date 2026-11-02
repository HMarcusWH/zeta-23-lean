"""Read the content-addressed research archive; never extract or execute it."""
from pathlib import Path, PurePosixPath
import argparse, hashlib, io, json, sys, zipfile

def require(ok,message):
    if not ok:raise ValueError(message)
def sha(b):return hashlib.sha256(b).hexdigest()
def safe(s):
    p=PurePosixPath(s)
    require(isinstance(s,str) and not p.is_absolute() and '..' not in p.parts and
            '\\' not in s and ':' not in s and p.as_posix()==s,'Invalid logical path')
    return s

def main():
    p=argparse.ArgumentParser(description=__doc__)
    mode=p.add_mutually_exclusive_group(required=True)
    mode.add_argument('--verify',action='store_true');mode.add_argument('--list',action='store_true')
    mode.add_argument('--show',metavar='LOGICAL_PATH')
    a=p.parse_args();root=Path(__file__).resolve().parent
    m=json.loads((root/'PORTABLE_ARCHIVE_MANIFEST.json').read_bytes())
    require(m['schema']=='OPICA_RESEARCH_PROVENANCE_ARCHIVE_V1' and m['RH']==m['Step4']=='OPEN','Archive schema/authority differs')
    rows=m['logical_files'];logical={};expected={}
    for r in rows:
        name=safe(r['logical_path']);require(name.casefold() not in logical,'Duplicate/case-aliased logical path')
        logical[name.casefold()]=r
        require(r['content_path']=='objects/'+r['sha256'] and len(r['sha256'])==64,'Content path differs')
        entry=(r['bytes'],r['sha256'])
        require(r['content_path'] not in expected or expected[r['content_path']]==entry,'Inconsistent shared content')
        expected[r['content_path']]=entry
    require(len(expected)==m['unique_objects'],'Object count differs')
    if a.list:
        for r in rows:print(r['logical_path'])
        return
    arc=m['archive'];require(arc['format']=='ZIP_DEFLATED_ORDERED_BYTE_PARTS_V1','Unknown archive transport')
    require(0<arc['bytes']<=1024**3 and arc['part_bytes']==7*1024**2,'Archive bounds differ')
    data=io.BytesIO();seen=set();whole=hashlib.sha256()
    for i,r in enumerate(arc['parts'],1):
        name=safe(r['path']);require(name==f'authored-research.zip.part{i:04d}' and name not in seen,'Part order differs')
        seen.add(name);path=root/name
        require(not path.is_symlink() and not (hasattr(path,'is_junction') and path.is_junction()),'Linked archive part')
        raw=path.read_bytes()
        require(len(raw)==r['bytes'] and 0<len(raw)<=arc['part_bytes'] and sha(raw)==r['sha256'],'Part hash/size differs')
        if i<len(arc['parts']):require(len(raw)==arc['part_bytes'],'Short nonfinal part')
        whole.update(raw);data.write(raw)
    require(data.tell()==arc['bytes'] and whole.hexdigest()==arc['sha256'],'Whole ZIP hash differs')
    data.seek(0)
    with zipfile.ZipFile(data) as z:
        infos=z.infolist();require(len(infos)==len(expected) and len({x.filename for x in infos})==len(infos),'ZIP count/duplicates differ')
        require(set(x.filename for x in infos)==set(expected),'ZIP inventory differs')
        total=0
        for x in infos:
            size,digest=expected[x.filename]
            require(x.file_size==size and not x.is_dir() and not x.flag_bits&1 and
                    (x.external_attr>>16)&0o170000==0o100000 and
                    x.compress_type in (zipfile.ZIP_STORED,zipfile.ZIP_DEFLATED),'Unexpected archive member')
            total+=size
        require(total<=4*1024**3,'Uncompressed archive budget exceeded')
        if a.show:
            key=safe(a.show).casefold();require(key in logical,'Unknown logical research path')
            r=logical[key];require(r['bytes']<=16*1024**2,'Display exceeds16MiB; use ZIP tools for this recorded large object')
            raw=z.read(r['content_path']);require(sha(raw)==r['sha256'],'Displayed object hash differs')
            sys.stdout.write(raw.decode('utf-8-sig'));return
        for x in infos:
            h=hashlib.sha256();count=0
            with z.open(x) as f:
                for block in iter(lambda:f.read(1024**2),b''):
                    count+=len(block);require(count<=x.file_size,'Object expanded beyond declared size');h.update(block)
            require(count==x.file_size and h.hexdigest()==expected[x.filename][1],'Object content hash differs')
    print(json.dumps({'status':'PASS_COMPLETE_ARCHIVE_INVENTORY_AND_CONTENT','logical_files':len(rows),
                      'unique_objects':len(expected),'uncompressed_bytes':total,'parts':len(arc['parts']),
                      'authority':'CONTENT_INTEGRITY_NOT_MATHEMATICAL_PROOF','RH':'OPEN','Step4':'OPEN'}))

if __name__=='__main__':main()

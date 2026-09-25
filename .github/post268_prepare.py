"""One-shot, hash-verified preservation of the supplied post268 audit corpus."""
from pathlib import Path, PurePosixPath
import hashlib, json, lzma, subprocess

ROOT=Path(__file__).resolve().parents[1]
BASE='ab545e71bfb1b11c647597bee014fad6d9ac291a'
DEST=ROOT/'research/RHRC/audits/post268/frozen'
PAYLOAD_HASH='f4bfdb70d345145c5249657d111b3e0324366226062ad91062258e8389a7a454'

def preserve():
    parts=[ROOT/f'.github/post268_archive/part{i:02}.bin' for i in range(11)]
    raw=b''.join(p.read_bytes() for p in parts)
    assert hashlib.sha256(raw).hexdigest()==PAYLOAD_HASH, 'archive transport hash mismatch'
    data=json.loads(lzma.decompress(raw))
    assert len(data)==102
    for name,text in data.items():
        rel=PurePosixPath(name)
        assert not rel.is_absolute() and '..' not in rel.parts and isinstance(text,str)
        p=DEST/name
        assert not p.is_symlink()
        p.parent.mkdir(parents=True,exist_ok=True)
        p.write_bytes(text.encode())
    rows=[]
    tree=subprocess.check_output(['git','ls-tree','-r','-z',BASE],cwd=ROOT)
    for entry in tree.split(b'\0'):
        if not entry: continue
        meta,path=entry.split(b'\t',1)
        mode,kind,sha=meta.decode().split()
        assert kind=='blob'
        content=subprocess.check_output(['git','cat-file','blob',sha],cwd=ROOT)
        rows.append({'git_blob':sha,'mode':'0o0','path':path.decode(),
                     'sha256':hashlib.sha256(content).hexdigest(),'size':len(content)})
    assert len(rows)==1207
    manifest=''.join(json.dumps(row,sort_keys=True)+'\n' for row in sorted(rows,key=lambda r:r['path']))
    (DEST/'results/file_manifest.jsonl').write_text(manifest)
    for line in (DEST/'BUNDLE_SHA256SUMS.txt').read_text().splitlines():
        expected,name=line.split('  ',1)
        p=DEST/name
        assert hashlib.sha256(p.read_bytes()).hexdigest()==expected, f'original hash mismatch: {name}'
    assert len([p for p in DEST.rglob('*') if p.is_file()])==103
    print('Original audit: all 103 files preserved byte-for-byte, including reconstructed manifest.')

if __name__=='__main__':
    preserve()

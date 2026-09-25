from pathlib import Path
import zipfile, os, subprocess, json, hashlib, collections, time
A=Path('/mnt/data/rh_audit'); root=A/'snapshot/zeta-23-lean-main'; zp=Path('/mnt/data/zeta-23-lean-main (6)(1).zip')
records=[]
with zipfile.ZipFile(zp) as z:
 for i in z.infolist():
  if i.is_dir(): continue
  path='/'.join(Path(i.filename).parts[1:]); p=root/path
  raw=p.read_bytes(); mode=(i.external_attr>>16)&0o777
  if mode: os.chmod(p,mode)
  records.append({'path':path,'size':len(raw),'sha256':hashlib.sha256(raw).hexdigest(),'git_blob':hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest(),'mode':oct(mode)})
subprocess.run(['git','init','--quiet'],cwd=root,check=True)
subprocess.run(['git','config','core.autocrlf','false'],cwd=root,check=True)
# An index is sufficient for graph census. Do not invent a commit or historical refs.
subprocess.run(['git','add','--force','--all'],cwd=root,check=True)
tree=subprocess.check_output(['git','write-tree'],cwd=root,text=True).strip()
s={'archive':str(zp),'archive_sha256':hashlib.sha256(zp.read_bytes()).hexdigest(),'archive_commit_comment':'ab545e71bfb1b11c647597bee014fad6d9ac291a','computed_git_tree':tree,'expected_live_tree':'0fdd3151c86989f7cf7123be322b3968e89e3263','tree_matches_live':tree=='0fdd3151c86989f7cf7123be322b3968e89e3263','file_count':len(records),'extensions':dict(collections.Counter(Path(r['path']).suffix for r in records)),'uncompressed_bytes':sum(r['size'] for r in records),'git_history_available':False,'git_index_added_for_census_only':True}
(A/'results/snapshot_identity.json').write_text(json.dumps(s,indent=2)+'\n')
(A/'results/file_manifest.jsonl').write_text(''.join(json.dumps(r,sort_keys=True)+'\n' for r in records))
print(json.dumps(s,indent=2))

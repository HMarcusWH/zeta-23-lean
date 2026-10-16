const path = require('path');
const fs = require('fs');
const {DefaultArtifactClient, ArtifactNotFoundError} = require(process.env.K3_ARTIFACT_MODULE);
const [name, file, destination] = process.argv.slice(2);
const stopName = 'k3-unrun460-negative-stop';
if (!/^k3-unrun460-cp-[0-9]{3}-[0-9]{3}$/.test(name) && !['preflight','recover-results','recover-checks',stopName].includes(name)) throw new Error('Unexpected checkpoint command');
async function recover(client) {
  const out = name === 'recover-results' ? file : destination;
  if (fs.existsSync(out)) throw new Error('Recovery destination already exists');
  fs.mkdirSync(out,{recursive:true});
  const names = name === 'recover-results'
    ? Array.from({length:460},(_,i)=>'k3-unrun460-result-'+i)
    : JSON.parse(fs.readFileSync(file,'utf8')).chunks.map(c=>'k3-unrun460-checked-'+c.id);
  const receipt={method:'EXACT_NAME_LOOKUP_NO_GLOBAL_LIST_TRUNCATION',downloaded:[],missing:[]};
  let cursor=0;
  await Promise.all(Array.from({length:8},async()=>{
    while(cursor<names.length) {
      const artifactName=names[cursor++];
      let artifact;
      try { artifact=(await client.getArtifact(artifactName)).artifact; }
      catch(e) { if(e instanceof ArtifactNotFoundError){receipt.missing.push(artifactName);continue;} throw e; }
      const target=name==='recover-results'?path.join(out,artifactName):out;
      await client.downloadArtifact(artifact.id,{path:target});
      receipt.downloaded.push({name:artifactName,id:artifact.id,digest:artifact.digest});
    }
  }));
  fs.writeFileSync(path.join(out,'exact-name-recovery.json'),JSON.stringify(receipt,null,2));
  console.log(JSON.stringify({downloaded:receipt.downloaded.length,missing:receipt.missing.length}));
}
async function main() {
  const client = new DefaultArtifactClient();
  if(name==='preflight') {
    const root=path.resolve(file);fs.mkdirSync(root,{recursive:false});
    const source=path.join(root,'preflight.json');
    fs.writeFileSync(source,JSON.stringify({run:process.env.GITHUB_RUN_ID,source:process.env.GITHUB_SHA,arithmetic_started:false}));
    const created=await client.uploadArtifact('k3-unrun460-preflight',[source],root,{retentionDays:30});
    const artifact=(await client.getArtifact('k3-unrun460-preflight')).artifact;
    if(artifact.id!==created.id) throw new Error('Artifact lookup did not preserve preflight identity');
    await client.downloadArtifact(artifact.id,{path:path.join(root,'roundtrip')});
    if(!fs.readFileSync(source).equals(fs.readFileSync(path.join(root,'roundtrip/preflight.json')))) throw new Error('Artifact roundtrip changed bytes');
    console.log(JSON.stringify({artifactId:artifact.id,roundtrip:true,arithmetic_started:false}));return;
  }
  if(name==='recover-results'||name==='recover-checks') return recover(client);
  let stopped = false;
  try { await client.getArtifact(stopName); stopped = true; }
  catch (e) { if (!(e instanceof ArtifactNotFoundError)) throw e; }
  if (stopped) { process.exitCode = name === stopName ? 0 : 42; return; }
  const x = await client.uploadArtifact(name, [path.resolve(file)], path.dirname(path.resolve(file)), {retentionDays: 30});
  console.log(JSON.stringify({artifactId:x.id, name}));
}
main().catch(e => { console.error(String(e)); process.exitCode=1; });

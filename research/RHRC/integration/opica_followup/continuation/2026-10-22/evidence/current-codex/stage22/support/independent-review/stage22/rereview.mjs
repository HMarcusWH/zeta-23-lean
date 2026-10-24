import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import {execFileSync} from 'node:child_process';
const cwd=process.cwd(), repo=path.join(cwd,'work/opica-followup-repo'), out=path.join(cwd,'work/audit-independent-contract-review/stage22');
const sha=b=>crypto.createHash('sha256').update(b).digest('hex');
const read=p=>fs.readFileSync(p,'utf8');
const frozen=JSON.parse(read(path.join(repo,'research/RHRC/integration/opica_followup/PUBLIC_ROOTS.json')));
const manifest=JSON.parse(read(path.join(repo,'research/RHRC/integration/opica_followup/BUILD_MANIFEST.json')));
const units=JSON.parse(read(path.join(repo,'research/RHRC/integration/opica_followup/PAPER_CROSSWALK.json'))).scope_units;
const overlay=path.join(cwd,'work/audit-release/overlay');
const overrides=Object.fromEntries(['NativeFilters','JointObservation','Consumers','Validation'].map(n=>['Zeta23/OPICAFollowup/'+n+'.lean',path.join(overlay,'Zeta23/OPICAFollowup/'+n+'.lean')]));
overrides['Zeta23/OPICAFollowup.lean']=path.join(overlay,'Zeta23/OPICAFollowup.lean');
overrides['Zeta23/OPICAFollowup/SquareDefect.lean']=path.join(cwd,'work/audit-square-physical/SquareDefectPhysicalFullCandidate.lean');
const sourceOf=p=>overrides[p]??path.join(repo,p);
function signatureEnd(s,start){let depth=0,comment=0,string=false;for(let i=start;i<s.length;i++){if(comment){if(s.slice(i,i+2)==='/-'){comment++;i++;}else if(s.slice(i,i+2)==='-/'){comment--;i++;}continue;}if(string){if(s[i]==='"'&&s[i-1]!=='\\')string=false;continue;}if(s.slice(i,i+2)==='/-'){comment++;i++;continue;}if(s.slice(i,i+2)==='--'){i=s.indexOf('\n',i);if(i<0)return s.length;continue;}if(s[i]==='"'){string=true;continue;}if('([{'.includes(s[i]))depth++;if(')]}'.includes(s[i]))depth--;if(depth===0&&s.slice(i,i+2)===':='&&!s.slice(s.lastIndexOf('\n',i)+1,i).trim().startsWith('let '))return i;}return s.length;}
function declaration(s,name){const re=new RegExp('(?:^|\\n)[ \\t]*(?:(?:private|protected|noncomputable) )?(?:theorem|lemma|def|abbrev|structure|inductive|opaque) '+name+'(?=[\\s{(:])','g');const m=[...s.matchAll(re)].at(-1);if(!m)return null;const start=m.index+(s[m.index]==='\n'?1:0);return {line:s.slice(0,start).split('\n').length,signature:s.slice(start,signatureEnd(s,start)).trim()};}
const validation=read(sourceOf('Zeta23/OPICAFollowup/Validation.lean'));
const companions=JSON.parse(read(path.join(cwd,'work/audit-release/full-signature-companion-provenance.json')));
const rows=frozen.roots.map((r,i)=>{const source=sourceOf(r.path);const text=read(source);const root=declaration(text,r.full_name.split('.').at(-1));const expected=declaration(validation,r.expected_type_consumer);const full=companions.find(c=>c.root===r.full_name);return {...r,index:i+1,source,source_sha256:sha(fs.readFileSync(source)),actual:root,required_expected:expected,full_signature_companion:full?{name:full.companion,...declaration(validation,full.companion.split('.').at(-1))}:null,status:'NONAUTHOR_SEMANTIC_REVIEW_IN_PROGRESS_NO_ACCEPTANCE'};});
const definitions=manifest.modules.filter(m=>m.trust_zone!=='AUDIT_ONLY').flatMap(m=>(m.required_definitions??[]).map(name=>{const source=sourceOf(m.path);const d=declaration(read(source),name);return {name,full_name:'Zeta23.OPICAFollowup.'+name,original_module:m.module,source,source_sha256:sha(fs.readFileSync(source)),...d,found:!!d};}));
const sources=Object.fromEntries(manifest.modules.map(m=>[m.path,{source:sourceOf(m.path),sha256:sha(fs.readFileSync(sourceOf(m.path)))}]));
fs.mkdirSync(out,{recursive:true});fs.writeFileSync(path.join(out,'ASSEMBLED_REVIEW_INPUT.json'),JSON.stringify({status:'NONAUTHOR_REVIEW_INPUT_NOT_A_SEAL',created_utc:new Date().toISOString(),owner_head:execFileSync('git',['rev-parse','HEAD'],{cwd:repo,encoding:'utf8'}).trim(),owner_tree:execFileSync('git',['rev-parse','HEAD^{tree}'],{cwd:repo,encoding:'utf8'}).trim(),owner_status:execFileSync('git',['status','--short'],{cwd:repo,encoding:'utf8'}),sources,rows,units,definitions},null,2));
const selected=process.argv[2]==='seven'?rows.filter(r=>r.full_signature_companion):process.argv[2]==='definitions'?definitions:rows.slice(Number(process.argv[2]??0),Number(process.argv[3]??0));
for(const r of selected)console.log(JSON.stringify(r,null,2));
console.log(JSON.stringify({roots:rows.length,required_consumers:rows.filter(r=>r.required_expected).length,full_signature_companions:rows.filter(r=>r.full_signature_companion).length,definitions:definitions.length,missing_definitions:definitions.filter(d=>!d.found).map(d=>d.name)}));

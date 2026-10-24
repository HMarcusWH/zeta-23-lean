import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
const root=process.cwd();
const sha=p=>crypto.createHash('sha256').update(fs.readFileSync(p)).digest('hex');
const dir=path.join(root,'work/audit-tempered-lattice');
const result=[];
for (const name of fs.readdirSync(dir).filter(n=>n.endsWith('.receipt.json'))) {
  const p=path.join(dir,name),r=JSON.parse(fs.readFileSync(p,'utf8'));
  if (!['cutoff7.receipt.json','bridge1.receipt.json','expected1.receipt.json','negative1.receipt.json','audit1.receipt.json'].includes(name)) continue;
  const log=path.join(dir,name.replace('.receipt.json','.log'));
  const checks=Object.entries(r.source_before??{}).filter(([p])=>p.endsWith('.lean')||p.endsWith('lean-toolchain')||p.endsWith('lake-manifest.json')).map(([p,h])=>({path:p,recorded_sha256:h,after_sha256:r.source_after?.[p],actual_sha256:fs.existsSync(p)?sha(p):null}));
  result.push({name,receipt_sha256:sha(p),exit_code:r.exit_code,source_unchanged:r.source_unchanged,head:r.head,tree:r.tree,compiler_version:r.compiler_version,log_sha256:r.log_sha256,actual_log_sha256:fs.existsSync(log)?sha(log):null,source_count:checks.length,all_sources_match:checks.every(c=>c.recorded_sha256===c.actual_sha256&&c.recorded_sha256===c.after_sha256),source_checks:checks.filter(c=>c.path.includes('audit-tempered-lattice')||c.path.includes('audit-square-physical'))});
}
const sources=['SchwartzCompactApprox.lean','TemperedLatticeNoRepair.lean','ExpectedTemperedLatticeNoRepair.lean','TemperedLatticeAxiomAudit.lean','NegativeOmitsCompactCompatibility.lean'].map(name=>{const p=path.join(dir,name);return{name,sha256:sha(p)}});
console.log(JSON.stringify({sources,receipts:result},null,2));

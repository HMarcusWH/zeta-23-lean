from fractions import Fraction as F
from math import comb, factorial, prod
import json,pathlib,hashlib,subprocess,datetime
H=pathlib.Path(__file__).resolve().parent
R=H.parent/'opica-followup-repo'
G='C:/Users/macka/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/git/cmd/git.exe'
PIN='9a8b2a4baee49f2056c7945b1544a7bc2893735b'
def det(A):
 A=[row[:] for row in A]; result=F(1)
 for j in range(len(A)):
  pivot=next((k for k in range(j,len(A)) if A[k][j]),None)
  if pivot is None: return F(0)
  if pivot!=j: A[j],A[pivot]=A[pivot],A[j]; result=-result
  v=A[j][j]; result*=v
  for k in range(j+1,len(A)):
   ratio=A[k][j]/v
   for l in range(j+1,len(A)): A[k][l]-=ratio*A[j][l]
 return result
def normalized_entry(n,k,kappa):
 # Hasse coefficient of X*(1/4-X)^n at kappa; computes the
 # polynomial independently, without the Lean determinant theorem.
 return sum((F(comb(n,s)) * F(1,4)**(n-s) * (-1)**s *
   comb(s+1,k) * kappa**(s+1-k) for s in range(n+1) if s+1>=k),F(0))
def check(name,nodes,multiplicities,scope):
 M=sum(multiplicities)
 columns=[(j,k) for j,m in enumerate(multiplicities) for k in range(m)]
 A=[[normalized_entry(n,k,nodes[j]) for j,k in columns] for n in range(M)]
 lhs=det(A)
 rhs=F((-1)**(M*(M-1)//2))*prod((x**m for x,m in zip(nodes,multiplicities)),start=F(1))*prod(
  ((nodes[j]-nodes[i])**(multiplicities[i]*multiplicities[j]) for j in range(len(nodes)) for i in range(j)),start=F(1))
 assert lhs==rhs,(name,lhs,rhs)
 raw=det([[A[n][i]*factorial(k) for i,(j,k) in enumerate(columns)] for n in range(M)])
 assert raw==lhs*prod((factorial(k) for _,k in columns),start=1)
 return {'name':name,'nodes':[str(x) for x in nodes],'multiplicities':multiplicities,
  'matrix':[[str(x) for x in row] for row in A],'normalized_det':str(lhs),'product_formula':str(rhs),
  'unnormalized_derivative_det':str(raw),'scope':scope,'result':'PASS'}
tests=[check('empty-system',[],[],'M=0 empty product'),
 check('all-zero-multiplicities',[F(2),F(5)],[0,0],'zero-dimensional algebra'),
 check('simple-node',[F(2)],[1],'one active node'),
 check('third-order-block',[F(2)],[3],'normalized k=2 column distinguishes omitted factorial'),
 check('mixed-blocks',[F(2),F(5)],[2,3],'M=5 cross gap exponent 6 and all factorials'),
 check('ordered-simple-blocks',[F(2),F(5)],[1,1],'orientation check'),
 check('reversed-simple-blocks',[F(5),F(2)],[1,1],'orientation sign reverses'),
 check('quarter-node',[F(1,4)],[3],'entire-family algebra at vanishing radicand'),
 check('zero-node',[F(0)],[1],'violates nonzero-node invertibility hypothesis'),
 check('collision',[F(2),F(2)],[1,1],'violates distinct-block node hypothesis'),
 check('dummy-block',[F(2),F(5)],[3,0],'zero block does not contribute a column')]
for q in [2,10,100,1000]:
 tests.append(check('near-collision-'+str(q),[F(2),F(2)+F(1,q)],[2,3],
  'auxiliary rational nodes, not invented zeta zeros; determinant degenerates as gap shrinks'))
files=['Zeta23/OPICAFollowup/ConfluentProfiles.lean','Zeta23/OPICAFollowup/CoPoissonJets.lean',
 'research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedConfluentProfiles.lean',
 'research/RHRC/integration/opica_followup/BUILD_SPEC.md','lean-toolchain','lake-manifest.json']
sources=[]
for rel in files:
 pinned=subprocess.check_output([G,'-C',str(R),'show',PIN+':'+rel])
 live=(R/rel).read_bytes()
 assert pinned==live,rel+' changed from reviewed code pin'
 sources.append({'path':rel,'commit':PIN,'sha256':hashlib.sha256(live).hexdigest(),'bytes':len(live)})
report={'schema':'OPICA_INDEPENDENT_H2A_MATH_REVIEW_CONTROLS_V1',
 'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reviewed_commit':PIN,
 'reviewed_tree':subprocess.check_output([G,'-C',str(R),'rev-parse',PIN+'^{tree}'],text=True).strip(),
 'sources':sources,'tests':tests,'status':'FIFTEEN_EXACT_RATIONAL_AUXILIARY_TESTS_PASS',
 'authority_limits':['Mathematical supporting audit by a non-author agent','Not a new Lean theorem receipt',
  'Not external human review','Not full-100 release seal','Rational algebra examples are not actual zeta zeros',
  'RH and Step4 remain OPEN']}
out=H/'H2A_MATH_REVIEW_CONTROLS_2026-10-24.json'
out.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'path':str(out),'sha256':hashlib.sha256(out.read_bytes()).hexdigest(),
 'cases':len(tests),'reviewed_sources_match_pin':len(sources)},indent=2))

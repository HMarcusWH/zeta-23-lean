"""Bounded point enclosures of the complete finite canonical source.

No sampled matrix is substituted for the zeta source. The fixed-unit producer
and direct-interval checker use the theorem-identified equation-(4.4) formula.
Finite interval evidence is not a Lean theorem or an asymptotic restriction.
"""
from __future__ import annotations
from fractions import Fraction as F
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import stat
import subprocess
import sys
from typing import Any

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[3]
ROUTE=REPO/'research/RHRC/routes/R003_ccm_bridge'
MAX_WIDTH=F(1,2**40)
CAPS={'full_core_accepted':False,'full_release_accepted':False,'human_review':'NOT_ESTABLISHED',
      'RH':'OPEN','Step4':'OPEN'}
INPUT_FIELDS={'id','K','Q','aperture'}
SEAMS={2,3,4,8,16}
ANCHORS=[
 'Zeta23.CCM.canonicalSourceMatrix_eq_sourceEq44Matrix',
 'Zeta23.CCM.sourceEq44GammaL_eq_cutoffFreeGammaL',
 'Zeta23.CCM.canonicalPrimeMatrix_eq_sum_sourceMatrix',
 'Zeta23.CCM.poleComponent_eq_profile_factorization',
 'Zeta23.CCM.poleNeutralEven_iff_exponentialMoments',
 'Zeta23.CCM.poleNeutralOdd_iff_exponentialMoments',
 'Zeta23.CCM.finrank_poleNeutralEvenSubspace',
 'Zeta23.CCM.finrank_poleNeutralOddSubspace',
 'Zeta23.CCM.poleNeutralCompressedIndexDefect_eq_projected_legal_add_residual',
 'Zeta23.CCM.poleNeutralCorrectedCubicSource_eq_explicitCanonicalSourceMoment',
 'Zeta23.CCM.qBasis_aperture_eq_zero',
]
SOURCE_PATHS=[
 'research/RHRC/integration/opica_round3/'+p for p in (
 'source_backend.py','source_evaluator.py','source_checker.py','fixtures/source_evaluator_cases.json',
 'schemas/source_evaluator.schema.json','tests/test_source_evaluator.py')]
SOURCE_PATHS += ['Zeta23/CCM/'+p+'.lean' for p in (
 'Components','SourceWeilMatrixReconciliation','SourceNormalizationRepair','CanonicalSourceChannels',
 'CanonicalSourceMomentAtoms','SourceMomentDecomposition','CanonicalPoleNeutralNormals',
 'CanonicalPoleNeutralCarrier','CanonicalPoleNeutralIntertwining','CanonicalPoleExponentialMoments',
 'QuadraticNormalMatrixMoment','BoundaryFlatFiniteSpace','ConstrainedParityGeometry',
 'KernelAnalysis','CanonicalApertureContinuity')]
SOURCE_PATHS += ['research/RHRC/routes/R003_ccm_bridge/'+p for p in (
 'canonical_source_arb.py','post175_fb05_q13_fixed_unit_enclosure.py','post290/residual_channels.py',
 'post290/native_seam_points.py')]
SOURCE_PATHS += ['research/RHRC/integration/opica_round2/certificate_io.py']


class InvalidRequest(ValueError): pass
class Unresolved(ArithmeticError): pass


def require(ok,message):
    if not ok: raise InvalidRequest(message)


def certain(ok,message):
    if not ok: raise Unresolved(message)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def identical(a,b):
    if type(a)is not type(b):return False
    if type(a)is dict:return set(a)==set(b) and all(identical(a[k],b[k]) for k in a)
    if type(a)is list:return len(a)==len(b) and all(identical(x,y) for x,y in zip(a,b))
    return a==b


def unlinked(path):
    """Check original path components before resolving any link/junction."""
    path=Path(os.path.abspath(path))
    for part in (path,*path.parents):
        try:info=os.lstat(part)
        except FileNotFoundError:continue
        require(not stat.S_ISLNK(info.st_mode) and not
                (getattr(info,'st_file_attributes',0)&getattr(stat,'FILE_ATTRIBUTE_REPARSE_POINT',1024)),
                'Linked/reparse evidence path refused')
    return path


def load_local(name,path):
    if name in sys.modules:
        module=sys.modules[name]
        require(Path(module.__file__).resolve()==path.resolve(),'Module namespace collision')
        return module
    spec=importlib.util.spec_from_file_location(name,path)
    require(spec is not None and spec.loader is not None,'Missing source module')
    module=importlib.util.module_from_spec(spec);sys.modules[name]=module
    spec.loader.exec_module(module)
    return module


def io():
    return load_local('_opica3_source_endpoint_io',REPO/'research/RHRC/integration/opica_round2/certificate_io.py')


def rational(text):
    try: return io().parse_rational(text)
    except ValueError as exc: raise InvalidRequest(str(exc)) from exc


def endpoint(text):
    try: return io().parse_endpoint_rational(text)
    except ValueError as exc: raise InvalidRequest(str(exc)) from exc


def strict_json(raw,limit=8*1024*1024):
    try:return io().loads_strict_json(raw,max_bytes=limit)
    except ValueError as exc:raise InvalidRequest(str(exc)) from exc


def source_identity(repo=REPO):
    repo=Path(repo).resolve()
    def git(*args):
        env={**os.environ,'GIT_NO_LAZY_FETCH':'1','GIT_TERMINAL_PROMPT':'0'}
        return subprocess.check_output(['git','-C',str(repo),*args],env=env,text=True).strip()
    return {'head':git('rev-parse','HEAD'),'tree':git('rev-parse','HEAD^{tree}'),
            'clean':not bool(git('status','--porcelain','--untracked-files=all')),
            'source_sha256':{p:digest(repo/p) for p in SOURCE_PATHS}}


def validate_request(case):
    require(type(case)is dict and set(case)==INPUT_FIELDS,'Closed point request required')
    require(type(case['id'])is str and re.fullmatch('[A-Za-z0-9_-]{1,64}',case['id']) is not None,'Bounded case ID required')
    require(type(case['K'])is int and case['K'] in (2,3),'Only exact K2/K3 supported')
    require(type(case['Q'])is int and 1<=case['Q']<=64,'Prime cutoff resource cap Q<=64')
    point=case['aperture']
    require(type(point)is dict,'Exact aperture constructor required')
    if point.get('kind')=='rational':
        require(set(point)=={'kind','value'},'Closed rational aperture required')
        require(rational(point['value'])>0,'Positive aperture required')
    elif point.get('kind')=='log_integer':
        require(set(point)=={'kind','n'} and type(point['n'])is int and point['n'] in SEAMS,
                'Registered exact symbolic logarithmic point required')
        require(case['Q']==point['n'],'Symbolic seam active floor must equal its integer')
    else: raise InvalidRequest('Unsupported aperture constructor')
    return case


def prime_powers(Q):
    rows=[]
    for q in range(2,Q+1):
        p=next((d for d in range(2,q+1) if q%d==0),q)
        remainder=q;power=0
        while remainder%p==0: remainder//=p;power+=1
        if remainder==1: rows.append((q,p,power))
    return rows


def symbolic_seed_checks():
    """Exact polynomial identities; no numerical zero test establishes legality."""
    # u_i(a)=constant_i+a*linear_i, on centered K3 indices.
    e1=[0,1,-4,6,-4,1,0];e2=[1,0,-9,16,-9,0,1]
    linear=[6*x-y for x,y in zip(e1,e2)]
    constant=[24*x-9*y for x,y in zip(e1,e2)]
    n=list(range(-3,4))
    for power in (0,2):
        require(sum(t**power*v for t,v in zip(n,linear))==0
                and sum(t**power*v for t,v in zip(n,constant))==0,'Seed moment polynomial failed')
    # Clear the explicit degree7 denominator product_i(a+n_i^2), then
    # multiply every integer coefficient. No point samples infer an identity.
    def multiply(x,y):
        out=[0]*(len(x)+len(y)-1)
        for i,a in enumerate(x):
            for j,b in enumerate(y):out[i+j]+=a*b
        return out
    for power in (0,2):
        numerator=[0]*8
        for i,t in enumerate(n):
            term=[constant[i],linear[i]]
            for j,s in enumerate(n):
                if j!=i:term=multiply(term,[s*s,1])
            for j,value in enumerate(term):numerator[j]+=t**power*value
        require(not any(numerator),'Cleared pole polynomial identity failed')
    for power,expected in ((0,[1764,1512,924]),(2,[6516,3528,756])):
        actual=[0]*3
        for t,c,l in zip(n,constant,linear):
            for i,v in enumerate((c*c,2*c*l,l*l)):actual[i]+=t**power*v
        require(actual==expected,'Seed norm polynomial identity failed')
    require(sum(t**4*v for t,v in zip(n,linear))==0
            and sum(t**4*v for t,v in zip(n,constant))==-720,'Nonzero seed fourth moment failed')
    return {'method':'EXPLICIT_INTEGER_COEFFICIENT_IDENTITIES_AFTER_CLEARING_DEGREE_7_DENOMINATOR',
            'parity_and_moments':[0,1,2],'pole_functionals':'EXACT_CONSTRUCTION',
            'M4':-720,'neutral_dimension_K3':1,'neutral_dimension_K2':0}


def rational_projectors(K):
    n=list(range(-K,K+1));N=len(n)
    q=[F(t*t)-F(sum(x*x for x in n),N) for t in n]
    q2=sum(x*x for x in q);n2=sum(t*t for t in n)
    E=[[F(int(i==j)+int(i==N-1-j),2)-F(1,N)-q[i]*q[j]/q2 for j in range(N)] for i in range(N)]
    O=[[F(int(i==j)-int(i==N-1-j),2)-F(n[i]*n[j],n2) for j in range(N)] for i in range(N)]
    return n,q,E,O


def evaluate_request(case,bits=128,representation='unit',export_bits=80):
    validate_request(case)
    require(type(bits)is int and 96<=bits<=1024,'Bounded precision96..1024 required')
    require(representation in ('unit','direct') and type(export_bits)is int and 48<=export_bits<=160,
            'Known representation and bounded export precision required')
    import flint
    from flint import acb,arb,arb_mat,ctx,fmpq
    certain(flint.__version__=='0.9.0','BACKEND_VERSION_UNAVAILABLE')
    C=load_local('_opica3_canonical_source_arb',ROUTE/'canonical_source_arb.py')
    previous=ctx.prec;ctx.prec=bits
    try:
        def ball(q):
            q=F(q);return arb(fmpq(q.numerator,q.denominator))
        def exact(value):
            m,e=value.man_exp();e=int(e)
            certain(abs(e)<=16384,'ENDPOINT_EXPONENT_BUDGET')
            return F(int(m))*F(2)**e
        def interval(value):
            certain(value.is_finite(),'NONFINITE_ENCLOSURE')
            low,high=exact(value.lower()),exact(value.upper())
            grid=2**export_bits
            low=F((low*grid).__floor__()-1,grid)
            high=F((high*grid).__ceil__()+1,grid)
            certain(high-low<=MAX_WIDTH,'INSUFFICIENT_ABSOLUTE_PRECISION')
            a,b=str(low),str(high)
            endpoint(a);endpoint(b)
            return {'lower':a,'upper':b}
        def matrix(M):return [[interval(M[i,j]) for j in range(M.ncols())] for i in range(M.nrows())]
        def vector(v):return [interval(v[i,0]) for i in range(v.nrows())]
        def dot(x,y):
            return sum((x[i,0]*y[i,0] for i in range(x.nrows())),arb(0))
        def convert(rows): return arb_mat([[ball(x) for x in row] for row in rows])
        K,Q=case['K'],case['Q'];point=case['aperture']
        L=ball(rational(point['value'])) if point['kind']=='rational' else arb(point['n']).log()
        certain(bool(L>0),'APERTURE_POSITIVITY_UNRESOLVED')
        if point['kind']=='rational':
            certain(C.fixed_cell_membership(Q,L)['certified'],'AMBIGUOUS_OR_WRONG_PRIME_FLOOR')
            active=Q;last=Q
            cutoff={'mode':'CERTIFIED_OPEN_CELL_POINT','active_Q':Q,'summed_through':Q,
                    'whole_input_ball_in_cell':True,'entering_atom':'NOT_A_SEAM'}
        else:
            active=Q;last=Q-1
            cutoff={'mode':'EXACT_SYMBOLIC_LOG_POINT','active_Q':Q,'summed_through':Q-1,
                    'whole_input_ball_in_cell':False,'entering_atom':'EXACT_ZERO_BY_qBasis_aperture_eq_zero'}
        tol=arb(2)**(-(bits-24));integral_options={'eval_limit':12000,'depth_limit':24,'deg_limit':128}
        def integral(func,end):
            z=acb.integral(lambda x,_analytic:func(x),acb(0),acb(end),
                rel_tol=tol,abs_tol=tol,**integral_options)
            certain(z.is_finite() and z.imag.contains(0),'QUADRATURE_RESOURCE_OR_NONFINITE_BOUND')
            return z.real
        indices=list(range(-K,K+1));alpha={};beta={};gamma={}
        for n in indices:
            if representation=='direct':
                alpha[n]=integral(lambda z:C._regularized_alpha_integrand(n,L,z),L)/arb.pi()
                beta[n]=integral(lambda z:C._regularized_beta_integrand(n,L,z),L)/L
                gamma[n]=integral(lambda z:C._regularized_gamma_integrand(n,L,z),L)+C.w_correction(L)
            else:
                a=acb(2*arb.pi()*n);lc=acb(L)
                alpha[n]=2*n*integral(lambda t:(a*t).sinc()*C._regularized_arch_scale(lc*t),arb(1))
                beta[n]=integral(lambda t:(a*t).cos()*C._regularized_arch_scale(lc*t),arb(1))
                gamma[n]=integral(lambda t:(a*C._cos_slope(a*t)+(lc/2)*C._exp_slope(-lc*t/2))*
                    C._regularized_arch_scale(lc*t),arb(1))+C.w_correction(L)
        atoms=prime_powers(last);N=len(indices)
        pole=arb_mat(N,N);adiag=arb_mat(N,N);aoff=arb_mat(N,N);prime=arb_mat(N,N)
        for i,n in enumerate(indices):
            for j,m in enumerate(indices):
                pole[i,j]=C.pole_component(n,m,L)
                if n==m:adiag[i,j]=2*gamma[n]-2*beta[n]
                else:aoff[i,j]=(alpha[m]-alpha[n])/(n-m)
                prime[i,j]=sum((arb(p).log()/arb(q).sqrt()*C.q_basis(n,m,arb(q).log(),L)
                                for q,p,_power in atoms),arb(0))
        M=pole-adiag-aoff-prime
        n,q,E0,O0=rational_projectors(K);E,O=convert(E0),convert(O0)
        n2=arb_mat([[ball(x)] for x in q]);nu=dot(n2,n2)
        D=arb_mat([[arb(n[i]) if i==j else arb(0) for j in range(N)] for i in range(N)])
        pe=arb_mat([[L/(L*L+16*arb.pi()**2*t*t)] for t in n])
        po=arb_mat([[4*arb.pi()*t/(L*L+16*arb.pi()**2*t*t)] for t in n])
        ge,go=E*pe,O*po;ge2,go2=dot(ge,ge),dot(go,go)
        certain(bool(ge2>0 and go2>0 and nu>0),'POLE_NORMAL_DENOMINATOR_UNRESOLVED')
        Qe,Qo=E-ge*ge.transpose()/ge2,O-go*go.transpose()/go2
        geometry={'even':{'legal_dimension':K-1,'neutral_dimension':K-2,'legal_projector':matrix(E),
            'pole_profile':vector(pe),'legal_normal':vector(ge),'normal_norm_sq':interval(ge2),'neutral_projector':matrix(Qe)},
            'odd':{'legal_dimension':K-1,'neutral_dimension':K-2,'legal_projector':matrix(O),
            'pole_profile':vector(po),'legal_normal':vector(go),'normal_norm_sq':interval(go2),'neutral_projector':matrix(Qo)}}
        if K==2:
            neutral={p:{'status':'EMPTY_BY_EXACT_CARRIER_DIMENSION','dimension':0,'rayleigh_bottom':None}
                     for p in ('even','odd')}
            correction={'status':'NOT_APPLICABLE_EMPTY_NEUTRAL_CARRIER'}
        else:
            symbolic_seed_checks();a=(L/(4*arb.pi()))**2
            e1=[0,1,-4,6,-4,1,0];e2=[1,0,-9,16,-9,0,1]
            u=arb_mat([[6*(a+4)*x-(a+9)*y] for x,y in zip(e1,e2)]);v=D*u
            un,vn=dot(u,u),dot(v,v)
            certain(bool(un>0 and vn>0),'NATIVE_SEED_GRAM_UNRESOLVED')
            def native(z,g):
                energy=dot(z,M*z)/g
                enclosed=interval(energy)
                return {'status':'FINITE_ONE_DIMENSIONAL_NATIVE_ENCLOSURE','dimension':1,'seed':vector(z),
                        'gram':interval(g),'rayleigh_bottom':enclosed,
                        'sign':'STRICT_POSITIVE' if endpoint(enclosed['lower'])>0 else
                               'STRICT_NEGATIVE' if endpoint(enclosed['upper'])<0 else 'UNRESOLVED_SIGN'}
            neutral={'even':native(u,un),'odd':native(v,vn)}
            residual=E*M*u-Qe*M*u
            raw=D*residual;projected=Qo*raw
            legal=O*M*(D*u)-D*(E*M*u)
            native_defect=Qo*M*(D*u)-D*(Qe*M*u)
            S=dot(n2,M*u)/nu;a2=dot(n2,pe)/nu;coefficient=dot(ge,E*M*u)/ge2
            S0=S-a2*coefficient
            cubic=Qo*arb_mat([[arb(t**3)] for t in n])
            correction={'status':'FINITE_ACTUAL_SOURCE_ENCLOSURES','source_moment':interval(S),
                'quadratic_normal_coefficient':interval(a2),'removed_output_coefficient':interval(coefficient),
                'corrected_source_moment':interval(S0),'even_output_residual':vector(residual),
                'raw_index_output_residual':vector(raw),'projected_odd_output_residual':vector(projected),
                'projected_legal_defect':vector(Qo*legal),'native_intertwining_defect':vector(native_defect),
                'neutral_cubic_vector':vector(cubic),'corrected_rank_one_vector':vector(cubic*S0),
                'identity_checks_are':'CONSISTENCY_ONLY_EXISTING_LEAN_IDENTITIES_SUPPLY_THEOREM_AUTHORITY'}
        q4=None
        if Q>=4 and last>=4:
            effect=-arb(2).log()/arb(4).sqrt()*C.q_basis(0,0,arb(4).log(),L)
            enclosed=interval(effect)
            q4={'full_00_minus_missing_4_00':enclosed,'weight':interval(arb(2).log()/2),
                'strict_negative':endpoint(enclosed['upper'])<0}
        enclosures={'aperture':interval(L),'components':{'pole':matrix(pole),'arch_diagonal':matrix(adiag),
            'arch_offdiagonal':matrix(aoff),'prime_power':matrix(prime),'w_correction':interval(C.w_correction(L))},
            'matrix_real':matrix(M),'primitives':{name:[interval(cache[n]) for n in indices]
                for name,cache in (('alpha',alpha),('beta',beta),('gamma_direct_eq44',gamma))},
            'geometry':geometry,'neutral':neutral,'source_correction':correction,'prime_power_4_effect':q4,
            'prime_power_atoms':[{'q':q,'prime':p,'exponent':power,'weight':interval(arb(p).log()/arb(q).sqrt())}
                                 for q,p,power in atoms]}
        return {'request':case,'status':'FINITE_ENCLOSURES','backend_version':flint.__version__,
            'representation':representation,'precision_bits':bits,'export_bits':export_bits,
            'cutoff':cutoff,'enclosures':enclosures,'construction':{
                'ambient_dimension':N,'matrix':'COMPLETE_CANONICAL_REAL_SYMMETRIC_HERMITIAN_ON_COMPLEX_CARRIER',
                'legal_constraints':'EXACT_CENTERED_MOMENTS_0_1_2_AND_REVERSAL_PARITY',
                'neutrality':'EXACT_SYMBOLIC_CONSTRUCTION_NOT_BALL_CONTAINS_ZERO',
                'source_basis':'EXACT_K3_POLE_NEUTRAL_POLYNOMIAL_SEED' if K==3 else 'EMPTY_NATIVE_K2',
                'source_theorem_anchors':ANCHORS},'budgets':{'prime_cutoff_cap':64,'cutoff_complete_through':active,
                'unaccounted_prime_terms':0,'archimedean':'COMPLETE_FINITE_INTEGRALS_PLUS_EXACT_CLOSED_W_CORRECTION',
                'quadrature':integral_options,'quadrature_tolerance_exponent':-(bits-24),
                'absolute_export_width_cap':str(MAX_WIDTH),'serialization':'OUTWARD_DYADIC_GRID_WITH_ONE_EXTRA_ULP',
                'kernel_and_ties':'NO_NUMERICAL_ZERO_OR_MULTIPLICITY_CERTIFICATION'},
            'authority':'FINITE_INTERVAL_EVIDENCE_ONLY','is_zero_generated_detector':False,**CAPS}
    finally: ctx.prec=previous

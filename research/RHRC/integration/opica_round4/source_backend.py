"""Physical K4/K5 source enclosures, never a kernel or universal inequality.

The retained Arb formula provider supplies the complete pole - direct Arch -
all von Mangoldt prime powers matrix.  The physical basis and generalized
metric are new: D is represented by the identity between *different metrics*.
Direct mode independently solves the defining constraints and integrates on
[0,L]; unit mode uses the explicit polynomial basis and [0,1].
"""
from __future__ import annotations
from fractions import Fraction as F
import hashlib
import json
import os
from pathlib import Path,PurePosixPath,PureWindowsPath
import re
import subprocess
import sys

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[3]
import importlib.util
_spec=importlib.util.spec_from_file_location('_opica4_retained_backend',HERE.parent/'opica_round3/source_backend.py')
R3=importlib.util.module_from_spec(_spec);sys.modules[_spec.name]=R3;_spec.loader.exec_module(R3)
InvalidRequest=R3.InvalidRequest
Unresolved=R3.Unresolved
require=R3.require
certain=R3.certain
digest=R3.digest
strict_json=R3.strict_json
rational=R3.rational
endpoint=R3.endpoint
identical=R3.identical
unlinked=R3.unlinked
CAPS=R3.CAPS
MAX_WIDTH=F(1,2**40)
SOURCE_PATHS=sorted(set(R3.SOURCE_PATHS+['research/RHRC/integration/opica_round4/'+p for p in (
 '__init__.py','source_backend.py','source_evaluator.py','source_checker.py',
 'fixtures/source_cases.json','tests/test_source_evaluator.py','schemas/source_evaluator.schema.json')]))


def recorded_root(value):
    """Original execution path is checked metadata, never an artifact read path."""
    require(type(value)is str and value,'Original producer output path required')
    p=PureWindowsPath(value) if re.match(r'^[A-Za-z]:[\\/]',value) else PurePosixPath(value)
    require(p.is_absolute() and '..' not in p.parts and str(p)==value,'Noncanonical producer path metadata')
    return p


def source_identity():
    env={**os.environ,'GIT_NO_LAZY_FETCH':'1','GIT_TERMINAL_PROMPT':'0'}
    def git(*args):return subprocess.check_output(['git','-C',str(REPO),*args],env=env,text=True).strip()
    return {'head':git('rev-parse','HEAD'),'tree':git('rev-parse','HEAD^{tree}'),
      'clean':not bool(git('status','--porcelain','--untracked-files=all')),
      'source_sha256':{p:digest(REPO/p) for p in SOURCE_PATHS}}


def validate_request(case):
    require(type(case)is dict and set(case)=={'id','K','Q','aperture','source','entering_atom'},'Closed source request required')
    require(type(case['id'])is str and re.fullmatch('[A-Za-z0-9_-]{1,64}',case['id']) is not None,'Bounded ID required')
    require(type(case['K'])is int and case['K'] in (4,5),'Physical K4/K5 only')
    require(type(case['Q'])is int and 1<=case['Q']<=64,'Q resource cap1..64')
    p=case['aperture'];require(type(p)is dict,'Exact aperture required')
    if p.get('kind')=='rational':
        require(set(p)=={'kind','value'} and rational(p['value'])>0,'Positive canonical rational required')
    elif p.get('kind')=='log_integer':
        require(set(p)=={'kind','n'} and type(p['n'])is int and p['n'] in (2,3,4,8,16) and case['Q']==p['n'],'Exact registered seam required')
    elif p.get('kind')=='scaled_log_integer':
        require(set(p)=={'kind','n','scale'} and type(p['n'])is int and p['n'] in (2,4,8) and rational(p['scale'])>1,'Exact entering point required')
    else:raise InvalidRequest('Unknown aperture constructor')
    s=case['source'];require(type(s)is dict and set(s)=={'kind','prime2_multiplier'},'Closed arithmetic identity required')
    require(s in ({'kind':'VON_MANGOLDT','prime2_multiplier':'1'},
                  {'kind':'MODIFIED_Q2_NOT_ZETA','prime2_multiplier':'1/2'}),'Unknown arithmetic identity')
    q=case['entering_atom'];require(q is None or type(q)is int and q in (2,4,8),'Registered entering prime power only')
    if q is not None:require(p['kind']=='scaled_log_integer' and p['n']==q,'Entering atom needs its own exact physical aperture')
    return case


def exact_basis_coefficients(K):
    """Polynomial coefficients c+l*a; free coordinates a+r² ensure full rank.

    For each r=3..K: sum u=sum n²u=sum u/(a+n²)=0 identically.
    Odd basis is n*u, hence the same exact neutral space and D bijection.
    """
    require(type(K)is int and K in (4,5),'K4/K5 basis only')
    rows=[]
    for r in range(3,K+1):
        r2=r*r
        x={0:(F(0),-F((r2-4)*(r2-1),2)),
           1:(F(r2*(r2-4),3),F(r2*(r2-4),3)),
           2:(-F(r2*(r2-1),3),-F(r2*(r2-1),12)),r:(F(r2),F(1))}
        rows.append([x.get(abs(n),(F(0),F(0))) for n in range(-K,K+1)])
    return rows


def require_exported_spectrum(boxes):
    bounds=[(endpoint(x['lower']),endpoint(x['upper'])) for x in boxes]
    certain(all(lo<=hi and not(lo<=0<=hi) for lo,hi in bounds),'UNRESOLVED_EXPORTED_NEAR_ZERO_NOT_KERNEL')
    certain(all(bounds[i][1]<bounds[i+1][0] for i in range(len(bounds)-1)),'UNRESOLVED_EXPORTED_SPECTRAL_CLUSTER')


def exact_grouped_projectors(rows,metric=None,source_row=None,source_vector=None):
    """Exact rational repeated-root control; group full eigenspaces, no vectors.

    Nonrational roots and defective operators are unresolved, never rounded to
    a multiple root. Production unresolved ball clusters likewise fail closed.
    """
    import sympy as sp
    require(type(rows)is list and 1<=len(rows)<=3 and all(len(r)==len(rows) for r in rows),'Small square matrix required')
    def smat(rows):return sp.Matrix([[sp.Rational(F(x).numerator,F(x).denominator) for x in r] for r in rows])
    A=smat(rows);I=sp.eye(A.rows);G=I if metric is None else smat(metric)
    certain(G.shape==A.shape and G==G.T and all(G[:i,:i].det()>0 for i in range(1,A.rows+1)) and G*A==A.T*G,'NOT_PHYSICALLY_SELFADJOINT')
    require((source_row is None)==(source_vector is None),'Both source covector and vector required')
    roots=A.eigenvals();certain(all(x.is_Rational for x in roots),'NONRATIONAL_EXACT_GROUP')
    out=[]
    for b,m in sorted(roots.items()):
        P=I
        for c in roots:
            if c!=b:P=P*(A-c*I)/(b-c)
        certain(A*P==b*P and P*P==P and sp.trace(P)==m,'DEFECTIVE_EXACT_GROUP')
        group={'eigenvalue':str(b),'multiplicity':int(m),'projector':[[str(P[i,j]) for j in range(A.cols)] for i in range(A.rows)]}
        if source_row is not None:
            require(len(source_row)==A.rows and len(source_vector)==A.rows,'Source dimensions mismatch')
            group['residue']=str((smat([source_row])*P*smat([source_vector]).T)[0,0])
        out.append(group)
    certain(sum((sp.Matrix([[sp.Rational(x) for x in r] for r in g['projector']]) for g in out),sp.zeros(A.rows))==I,'INCOMPLETE_EXACT_GROUPS')
    return out


def evaluate_request(case,bits=256,representation='unit',export_bits=80):
    validate_request(case)
    require(type(bits)is int and bits in (256,512,1024),'Precision256/512/1024 required')
    require(representation in ('unit','direct') and type(export_bits)is int and 64<=export_bits<=160,'Known representation/export budget required')
    import flint
    from flint import arb,acb,arb_mat,ctx,fmpq
    certain(flint.__version__=='0.9.0','BACKEND_VERSION_UNAVAILABLE')
    C=R3.load_local('_opica3_canonical_source_arb',R3.ROUTE/'canonical_source_arb.py')
    previous=ctx.prec;ctx.prec=bits
    try:
        def ball(q):
            q=F(q);return arb(fmpq(q.numerator,q.denominator))
        def exact(x):
            m,e=x.man_exp();e=int(e);certain(abs(e)<=16384,'ENDPOINT_EXPONENT_BUDGET');return F(int(m))*F(2)**e
        def interval(x):
            certain(x.is_finite(),'NONFINITE_ENCLOSURE')
            grid=2**export_bits;lo=F((exact(x.lower())*grid).__floor__()-1,grid);hi=F((exact(x.upper())*grid).__ceil__()+1,grid)
            certain(hi-lo<=MAX_WIDTH,'INSUFFICIENT_ABSOLUTE_PRECISION')
            return {'lower':str(lo),'upper':str(hi)}
        def mat(A):return [[interval(A[i,j]) for j in range(A.ncols())] for i in range(A.nrows())]
        def vec(A):return [interval(A[i,0]) for i in range(A.nrows())]
        def dot(x,y):return (x.transpose()*y)[0,0]
        def col(v):return arb_mat([[x] for x in v])
        def zeros(A):return all(A[i,j].contains(0) for i in range(A.nrows()) for j in range(A.ncols()))
        def det(A):return A.det()
        K,Q=case['K'],case['Q'];N=2*K+1;d=K-2;ns=list(range(-K,K+1));p=case['aperture']
        L=ball(rational(p['value'])) if p['kind']=='rational' else arb(p['n']).log()*(ball(rational(p['scale'])) if p['kind']=='scaled_log_integer' else 1)
        certain(bool(L>0),'APERTURE_POSITIVITY_UNRESOLVED')
        if p['kind']=='log_integer':
            last=Q-1;cutoff={'mode':'EXACT_SYMBOLIC_LOG_POINT','active_Q':Q,'summed_through':last,'whole_input_ball_in_cell':False,'entering_atom':'EXACT_ZERO_BY_qBasis_aperture_eq_zero'}
        else:
            certain(C.fixed_cell_membership(Q,L)['certified'],'AMBIGUOUS_OR_WRONG_PRIME_FLOOR')
            last=Q;cutoff={'mode':'CERTIFIED_OPEN_CELL_POINT','active_Q':Q,'summed_through':last,'whole_input_ball_in_cell':True,'entering_atom':'NOT_A_SEAM'}
        tol=arb(2)**(-(bits-32));options={'eval_limit':16000,'depth_limit':26,'deg_limit':128}
        def integral(func,end):
            z=acb.integral(lambda x,_analytic:func(x),acb(0),acb(end),rel_tol=tol,abs_tol=tol,**options)
            certain(z.is_finite() and z.imag.contains(0),'QUADRATURE_RESOURCE_OR_NONFINITE_BOUND');return z.real
        alpha={};beta={};gamma={}
        for n in ns:
            if representation=='direct':
                alpha[n]=integral(lambda z:C._regularized_alpha_integrand(n,L,z),L)/arb.pi()
                beta[n]=integral(lambda z:C._regularized_beta_integrand(n,L,z),L)/L
                gamma[n]=integral(lambda z:C._regularized_gamma_integrand(n,L,z),L)+C.w_correction(L)
            else:
                a0=acb(2*arb.pi()*n);lc=acb(L)
                alpha[n]=2*n*integral(lambda t:(a0*t).sinc()*C._regularized_arch_scale(lc*t),arb(1))
                beta[n]=integral(lambda t:(a0*t).cos()*C._regularized_arch_scale(lc*t),arb(1))
                gamma[n]=integral(lambda t:(a0*C._cos_slope(a0*t)+(lc/2)*C._exp_slope(-lc*t/2))*C._regularized_arch_scale(lc*t),arb(1))+C.w_correction(L)
        atoms=R3.prime_powers(last);pole=arb_mat(N,N);ad=arb_mat(N,N);ao=arb_mat(N,N);prime=arb_mat(N,N)
        multiplier=ball(rational(case['source']['prime2_multiplier']))
        for i,n in enumerate(ns):
            for j,m in enumerate(ns):
                pole[i,j]=C.pole_component(n,m,L)
                if n==m:ad[i,j]=2*(gamma[n]-beta[n])
                else:ao[i,j]=(alpha[m]-alpha[n])/(n-m)
                prime[i,j]=sum((arb(pr).log()/arb(q).sqrt()*C.q_basis(n,m,arb(q).log(),L)*(multiplier if q==2 else 1) for q,pr,_ in atoms),arb(0))
        M=pole-ad-ao-prime
        a=(L/(4*arb.pi()))**2
        if representation=='unit':
            columns=[[ball(c)+ball(l)*a for c,l in row] for row in exact_basis_coefficients(K)]
        else:
            # Independent defining-equation solve, using rational a-normalized pole functional.
            piv=(0,1,2);constraints=arb_mat([[arb(1 if n==0 else 2) for n in piv],
                [arb(2*n*n) for n in piv],[arb(1 if n==0 else 2)/(a+n*n) for n in piv]])
            certain(not constraints.det().contains(0),'POLE_BASIS_SOLVE_UNRESOLVED');columns=[]
            for r in range(3,K+1):
                free=a+r*r;rhs=col([-2*free,-2*r*r*free,-arb(2)])
                coeff=constraints.solve(rhs);values={0:coeff[0,0],1:coeff[1,0],2:coeff[2,0],r:free}
                columns.append([values.get(abs(n),arb(0)) for n in ns])
        Te=arb_mat([[columns[j][i] for j in range(d)] for i in range(N)])
        D=arb_mat([[arb(n) if i==j else arb(0) for j in range(N)] for i,n in enumerate(ns)])
        To=D*Te;Ge=Te.transpose()*Te;Go=To.transpose()*To
        for G in (Ge,Go):
            for size in range(1,d+1):certain(bool(arb_mat([[G[i,j] for j in range(size)] for i in range(size)]).det()>0),'PHYSICAL_GRAM_NOT_CERTIFIED_POSITIVE')
        He=Te.transpose()*M*Te;Ho=To.transpose()*M*To;A=Ge.solve(He);B=Go.solve(Ho)
        _,q,E0,O0=R3.rational_projectors(K)
        E=arb_mat([[ball(x) for x in row] for row in E0]);O=arb_mat([[ball(x) for x in row] for row in O0])
        pe=col([L/(L*L+16*arb.pi()**2*n*n) for n in ns]);po=col([4*arb.pi()*n/(L*L+16*arb.pi()**2*n*n) for n in ns])
        ge=E*pe;go=O*po;ge2=dot(ge,ge);go2=dot(go,go)
        certain(bool(ge2>0 and go2>0),'POLE_NORMAL_DENOMINATOR_UNRESOLVED')
        Qe=E-ge*ge.transpose()/ge2;Qo=O-go*go.transpose()/go2
        qv=col([ball(x) for x in q]);nu=dot(qv,qv)
        S=qv.transpose()*M*Te/nu;a2=dot(qv,pe)/nu;removed=ge.transpose()*E*M*Te/ge2;f=S-removed*a2
        cubic=Qo*col([arb(n**3) for n in ns]);g=Go.solve(To.transpose()*cubic)
        residual=E*M*Te-Qe*M*Te;raw=D*residual;projected=Qo*raw
        native=Qo*M*To-D*Qe*M*Te;legal=Qo*(O*M*To-D*E*M*Te)
        rank=B-A-g*f
        certain(zeros(rank) and zeros(native-cubic*f) and zeros(native-legal-projected),'CORRECTED_INTERTWINING_CONSISTENCY_FAILED')
        I=arb_mat([[arb(int(i==j)) for j in range(d)] for i in range(d)])
        def spectrum(T,G,H):
            try:roots=T.eig(algorithm='rump')
            except (ValueError,ArithmeticError) as exc:raise Unresolved('UNRESOLVED_SPECTRAL_CLUSTER') from exc
            certain(all(z.is_finite() and z.imag.contains(0) for z in roots),'NONREAL_OR_NONFINITE_SPECTRUM')
            roots=sorted([z.real for z in roots],key=lambda x:exact(x.mid()))
            # Explicit sign-changing characteristic brackets exhaust degree d;
            # selfadjointness is with the independently positive physical G.
            margin=arb(2)**(-min(180,bits//2-16));brackets=[]
            for x in roots:
                lo=x.lower()-margin;hi=x.upper()+margin
                pl=(G*lo-H).det()/G.det();ph=(G*hi-H).det()/G.det()
                certain(bool(pl*ph<0),'GENERALIZED_ROOT_BRACKET_UNRESOLVED')
                brackets.append(arb((lo+hi)/2,(hi-lo)/2))
            certain(all(bool(brackets[j]<brackets[j+1]) for j in range(d-1)),'UNRESOLVED_SPECTRAL_CLUSTER')
            certain(all(not x.contains(0) for x in brackets),'UNRESOLVED_NEAR_ZERO_NOT_KERNEL')
            require_exported_spectrum([interval(x) for x in brackets])
            return brackets
        ea=spectrum(A,Ge,He);eb=spectrum(B,Go,Ho);residues=[];projectors=[];ratios=[]
        for i,b in enumerate(eb):
            P=I;den=arb(1)
            for j,c in enumerate(eb):
                if i!=j:P=P*(B-I*c)/(b-c);den*=b-c
            c=(f*P*g)[0,0];ratio=arb(1)
            for x in ea:ratio*=b-x
            ratio/=den
            certain((c-ratio).contains(0),'SPECTRAL_RESIDUE_DISAGREEMENT')
            certain(not c.contains(0),'RESIDUE_SIGN_UNRESOLVED')
            require_exported_spectrum([interval(c)])
            residues.append(c);ratios.append(ratio);projectors.append(P)
        signed=sum((c/b for c,b in zip(residues,eb)),arb(0))
        positive=sum((c/b for c,b in zip(residues,eb) if bool(c>0)),arb(0))
        determinant_ratio=A.det()/B.det();endpoint_residual=1-signed-determinant_ratio
        certain(endpoint_residual.contains(0),'SIGNED_ENDPOINT_DETERMINANT_IDENTITY_DISAGREEMENT')
        derivatives={t:interval(sum((c/(b+ball(rational(t)))**2 for c,b in zip(residues,eb)),arb(0))) for t in ('0','21/50','43/100')}
        def spectral(eigen,G,H,T):
            return {'dimension':d,'basis':mat(Te if T is A else To),'gram':mat(G),'form':mat(H),'operator':mat(T),
                'eigenvalues':[interval(x) for x in eigen],'negative_index':sum(bool(x<0) for x in eigen),
                'zero_index':0,'positive_index':sum(bool(x>0) for x in eigen),
                'root_method':'DISJOINT_SIGN_CHANGING_GENERALIZED_CHARACTERISTIC_BRACKETS'}
        atom=None
        if case['entering_atom'] is not None:
            q0=case['entering_atom'];pr=R3.prime_powers(q0)[-1][1]
            Hq=arb_mat([[arb(pr).log()/arb(q0).sqrt()*C.q_basis(n,m,arb(q0).log(),L)*(multiplier if q0==2 else 1) for m in ns] for n in ns])
            atom={'q':q0,'source':'ENTERING_ATOM_ONLY_NOT_COMPLETE_SOURCE','matrix':mat(Hq),'parities':{}}
            for name,T in (('even',Te),('odd',To)):
                compressed=T.transpose()*Hq*T;minor=arb_mat([[compressed[i,j] for j in range(2)] for i in range(2)]);delta=minor.det()
                certain(bool(delta<0),'ENTERING_ATOM_INDEFINITENESS_UNRESOLVED')
                atom['parities'][name]={'two_vector_form':mat(minor),'determinant':interval(delta),'signature':'ONE_POSITIVE_ONE_NEGATIVE'}
        source_id={'kind':case['source']['kind'],'prime2_multiplier':case['source']['prime2_multiplier'],
            'formula':'POLE_MINUS_DIRECT_ARCH_MINUS_COMPLETE_PRIME_POWERS','modified_q2_does_not_modify_q4':True}
        enclosures={'aperture':interval(L),'components':{'pole':mat(pole),'arch_diagonal':mat(ad),'arch_offdiagonal':mat(ao),'prime_power':mat(prime),'w_correction':interval(C.w_correction(L))},
            'matrix_real':mat(M),'physical':{'even':spectral(ea,Ge,He,A),'odd':spectral(eb,Go,Ho,B)},
            'transfer':{'coordinate_matrix':mat(I),'domain_metric':mat(Ge),'codomain_metric':mat(Go),'unitary_claim':False},
            'correction':{'source_moment':mat(S),'quadratic_normal_coefficient':interval(a2),'removed_output_coefficient':mat(removed),
                'corrected_source_row':mat(f),'cubic_coordinate_vector':vec(g),'even_output_residual':mat(residual),
                'raw_index_output_residual':mat(raw),'projected_odd_output_residual':mat(projected),'projected_legal_defect':mat(legal),
                'native_intertwining_defect':mat(native),'rank_one_residual':mat(rank),'pole_normal_norms':[interval(ge2),interval(go2)]},
            'spectrum':{'groups':[{'eigenvalue':interval(b),'multiplicity':1,'projector':mat(P),'residue':interval(c),'characteristic_residue':interval(r)} for b,P,c,r in zip(eb,projectors,residues,ratios)],
                'signed_response_at_zero':interval(signed),'positive_reciprocal_mass':interval(positive),'residue_sum':interval(sum(residues,arb(0))),
                'determinant_ratio':interval(determinant_ratio),'endpoint_determinant_identity_residual':interval(endpoint_residual),
                'negative_derivative_at_minus_t':derivatives},'entering_atom_control':atom,
            'prime_power_atoms':[{'q':q,'prime':pr,'exponent':power,'multiplier':case['source']['prime2_multiplier'] if q==2 else '1',
                'weight':interval(arb(pr).log()/arb(q).sqrt()*(multiplier if q==2 else 1))} for q,pr,power in atoms]}
        return {'schema':'OPICA4_FINITE_SOURCE_CASE_V1','request':case,'status':'FINITE_ENCLOSURES','backend_version':flint.__version__,
            'representation':representation,'precision_bits':bits,'export_bits':export_bits,'source':source_id,'cutoff':cutoff,'enclosures':enclosures,
            'construction':{'ambient_dimension':N,'neutral_dimension':d,'basis':'EXACT_POLYNOMIAL_POLE_NEUTRAL_FREE_INDICES_3_TO_K',
                'metric':'AMBIENT_EUCLIDEAN_PULLBACK_NO_UNITARY_TRANSFER','source_theorem_anchors':R3.ANCHORS,
                'clusters':'SIMPLE_SOURCE_GROUPS;EXACT_RATIONAL_REPEATED_ROOT_CONTROLS;UNRESOLVED_BALL_CLUSTERS_REJECT'},
            'budgets':{'prime_cutoff_cap':64,'unaccounted_prime_terms':0,'quadrature':options,'quadrature_tolerance_exponent':-(bits-32),
                'absolute_export_width_cap':str(MAX_WIDTH),'kernel_and_ties':'NO_NUMERICAL_ZERO_OR_MULTIPLICITY_CERTIFICATION'},
            'authority':'FINITE_INTERVAL_EVIDENCE_ONLY','is_zero_generated_detector':False,**CAPS}
    finally:ctx.prec=previous

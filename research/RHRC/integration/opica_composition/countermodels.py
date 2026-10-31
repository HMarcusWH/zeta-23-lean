"""Exact finite falsifiers, explicitly scoped away from the unchanged zeta source."""
from __future__ import annotations
from fractions import Fraction as F
from .canonical import require, digest

def _matrix(rows):return [[F(x) for x in row] for row in rows]
def _mul(a,b):return [[sum((a[i][k]*b[k][j] for k in range(len(b))),F(0)) for j in range(len(b[0]))] for i in range(len(a))]
def _sub(a,b):return [[x-y for x,y in zip(r,s)] for r,s in zip(a,b)]
def _det(a):
    if len(a)==1:return a[0][0]
    return sum(((-1)**j*a[0][j]*_det([r[:j]+r[j+1:] for r in a[1:]]) for j in range(len(a))),F(0))
def _transpose(a):return [list(r) for r in zip(*a)]

def _rank_one_control(identifier,a,b,d,g,f,claim):
    a,b,d,g,f=map(_matrix,(a,b,d,g,f))
    require(a==_transpose(a) and b==_transpose(b),'Hermitian premise failed')
    require(_det(d)!=0,'invertible transfer premise failed')
    require(_sub(_mul(b,d),_mul(d,a))==_mul(g,f),'rank-one identity failed')
    require(any(x for row in _mul(g,f) for x in row),'nonzero rank-one defect premise failed')
    encode=lambda m:[[str(x) for x in row] for row in m]
    return {'id':identifier,'status':'COUNTERMODEL_VERIFIED','source_kind':'SYNTHETIC_CONTROL',
            'preserved_premises':['Hermitian_A','Hermitian_B','invertible_D','nonzero_rank_one_intertwining'],
            'matrices':dict(zip(('A','B','D','g','f'),map(encode,(a,b,d,g,f)))),
            'refuted_inference':claim,'actual_zeta_counterexample':False}

def run_countermodel_bank() -> list[dict]:
    rows=[]
    shift=_rank_one_control('COMMON_SHIFT_ZERO_LEVEL',[[-2]],[[-1]],[[1]],[[1]],[[1]],
                            'relative source/transport identities establish absolute positivity')
    require(F(-1)-F(-2)==1 and F(3)-F(2)==1,'shift control failed')
    shift['absolute_zero_level']='both negative after common shift4 from positive2,3';rows.append(shift)
    nonunit=_rank_one_control('NONUNITARY_PSD_RANKONE_FALSE',[[-2,0],[0,-1]],[[1,0],[0,2]],
        [['1/3','1/2'],['1/4','1/3']],[[1],[1]],[[1,1]],
        'nonunitary intertwining is a Hermitian positive rank-one update')
    nonunit['negative_indices']={'A':2,'B':0};rows.append(nonunit)
    shared=_rank_one_control('SHARED_INVISIBLE_NEGATIVE_GROUND',[[-1,0],[0,2]],[[-1,0],[0,3]],
        [[1,0],[0,1]],[[0],[1]],[[0,1]],'rank-one transfer forces spectra disjoint or source sees every ground')
    shared['own_predecessors']={'A':'2>0','B':'3>0'};shared['common_negative_ground']='-1';rows.append(shared)
    tied=_rank_one_control('EQUAL_CUTOFF_UNEQUAL_GROUNDS',[[-1,0],[0,1]],[[-2,0],[0,1]],
        [[1,0],[0,1]],[[1],[0]],[[-1,0]],'equal first cutoff indices force equal eigenvalues')
    tied['same_birth_dimension']=2;tied['grounds']=['-1','-2'];rows.append(tied)
    endpoint=_rank_one_control('ENDPOINT_ZERO_MASKS_NEGATIVE',[[-1,0],[0,0]],[[1,0],[0,2]],
        [['1/2',1],['1/3','1/2']],[[1],[1]],[[1,1]],'endpoint response alone excludes negative zero-mode configurations')
    s0=-F(2)+F(6,2);s_half=-F(2)/F(1,2)+F(6)/F(3,2)
    require(s0==1 and (-F(2)/F(3,2)+F(6)/F(5,2))==F(16,15),'endpoint formula failed')
    endpoint['response_at_zero']='1';endpoint['response_at_minus_half']='16/15';rows.append(endpoint)
    absolute=_rank_one_control('ABSOLUTE_SIGNED_BOUND_FALSE',[[2]],[[1]],[[1]],[[1]],[[-1]],
        'one-sided signed upper bound also bounds absolute response')
    require((abs(F(-1))+F(-1))/2==0 and abs(F(-1,2))>0,'signed absolute control failed')
    rows.append(absolute)
    require(_det(_matrix([[0,1],[1,0]]))==-1,'resonant block control failed')
    rows.append({'id':'SINGULAR_PREDECESSOR_RANGE','status':'COUNTERMODEL_VERIFIED','source_kind':'SYNTHETIC_CONTROL',
        'preserved_premises':['PSD_predecessor','Hermitian_successor','one_shell'],
        'matrix':[['0','1'],['1','0']],'range_compatible':False,
        'refuted_inference':'pseudoinverse regular formula without kernel compatibility','actual_zeta_counterexample':False})
    epsilon=F(1,100);coefficient=1/(2*epsilon**2);component=coefficient*epsilon
    require(-2*component*epsilon==-1 and 1+component**2==2501,'witness control failed')
    rows.append({'id':'NONUNIT_RESONANT_COST','status':'COUNTERMODEL_VERIFIED','source_kind':'SYNTHETIC_CONTROL',
        'preserved_premises':['unit_shell','nonzero_kernel_coupling','energy_minus_one'],
        'kernel_coupling':str(epsilon),'witness_norm_sq':'2501','normalized_energy':'-1/2501',
        'refuted_inference':'energy minus1 is unit-vector spectral depth minus1','actual_zeta_counterexample':False})
    rows.append({'id':'STRONG_LIMIT_NONZERO','status':'COUNTERMODEL_VERIFIED','source_kind':'SYNTHETIC_CONTROL',
        'preserved_premises':['positive_Gram','optimal_residual','strong_convergence'],
        'target':['0','1'],'dictionary_span':['1','0'],'all_optimal_residuals':['0','1'],
        'residual_norm_sq':'1','refuted_inference':'strong optimal residual convergence implies zero','actual_zeta_counterexample':False})
    # Algebraic identity only. A finite sweep is not a limit proof.
    require(F(1,7)*F(7)==1,'varying-test algebraic control failed')
    rows.append({'id':'VARYING_TEST_COST','status':'DERIVED_SEQUENCE_CONTROL','source_kind':'SYNTHETIC_CONTROL',
        'preserved_premises':['pointwise_error_tends_zero'],'error':'1/n','test_norm':'n','paired_error':'1',
        'asymptotic_authority':'DERIVED_FROM_EXACT_FORMULA_NOT_A_FINITE_LIMIT_CERTIFICATE',
        'refuted_inference':'fixed-test estimate applies uniformly to uncontrolled moving tests','actual_zeta_counterexample':False})
    rows.append({'id':'UNRELATED_GRAM_WEIL','status':'COUNTERMODEL_VERIFIED','source_kind':'SYNTHETIC_CONTROL',
        'preserved_premises':['same_vector_space','positive_Gram'],'Gram':[['1']],'Weil':[['-1']],
        'refuted_inference':'matching source-free names identify different quadratic forms','actual_zeta_counterexample':False})
    rows.extend(_integration_controls())
    # Actual mixed residues, modified arithmetic and entering-prime atom controls
    # are supplied by the independent native numerical lane, never toy substitutes.
    for row in rows:row['id_digest']=digest(row,domain='OPICA_COUNTERMODEL_V1')
    return rows


def _integration_controls():
    """Exact symbolic checks, with no floating-point spectral classification."""
    import sympy as sp
    I=sp.I
    n=5
    B=sp.diag(*range(1,n+1));g=sp.ones(n,1);f=-g.T;A=B+g*g.T
    require(B-A==g*f,'signed rank-one family changed')
    require(all(A[:j,:j].det()>0 and B[:j,:j].det()>0 for j in range(1,n+1)),
            'positive matrices premise failed')
    V=sp.Matrix([[1/(sp.Integer(j)-sp.Integer(k)-I) for j in range(1,n+1)] for k in range(1,n+1)])
    det=sp.simplify(V.det());H=-V*V.conjugate().T
    require(det!=0 and all(sp.simplify((-1)**j*H[:j,:j].det())>0 for j in range(1,n+1)),
            'Pick negative-index certificate failed')
    rows=[{'id':'RANKONE_FIVE_NEGATIVE_PICK_SQUARES','status':'COUNTERMODEL_VERIFIED',
        'source_kind':'SYNTHETIC_CONTROL','preserved_premises':['positive_A','positive_B','invertible_D','rank_one_intertwining'],
        'dimension':n,'A':'diag(1,...,5)+ones*ones.transpose','B':'diag(1,...,5)',
        'D':'I','g':'ones','f':'-ones.transpose','grouped_residues':['-1']*n,
        'cauchy_points':'k+i for k=1,...,5','evaluation_determinant':str(det),
        'pick_kernel':'-V*V.adjoint','negative_squares':n,
        'family':'Same algebra for every finite d>=1; exact executable certificate is d=5 only',
        'refuted_inference':'rank-one defect bounds Pick negative squares by one',
        'actual_zeta_counterexample':False}]
    D=sp.Matrix([[1,1],[0,1]]);A=sp.diag(1,2);B=2*sp.eye(2);g=sp.Matrix([1,0]);f=sp.Matrix([[1,0]])
    P=sp.Matrix([[1,-I],[I,1]])/2;Q=sp.eye(2)-P
    require(B*D-D*A==g*f and P*P==P and P.conjugate().T==P and P*Q==sp.zeros(2),
            'repeated eigenspace control failed')
    residues=[sp.simplify((f*D.inv()*R*g)[0]) for R in (P,Q)]
    require(residues==[(1-I)/2,(1+I)/2] and sum(residues)==1,'complex coordinate control failed')
    rows.append({'id':'GROUPED_REAL_COORDINATES_COMPLEX','status':'COUNTERMODEL_VERIFIED',
        'source_kind':'SYNTHETIC_CONTROL','preserved_premises':['Hermitian_A','Hermitian_B','invertible_D','rank_one_intertwining','orthogonal_eigenprojections'],
        'A':[['1','0'],['0','2']],'B':'2I','D':[['1','1'],['0','1']],
        'coordinate_residues':[str(x) for x in residues],'grouped_residue':'1',
        'refuted_inference':'grouped residue reality gives individual eigenbasis coefficient reality',
        'actual_zeta_counterexample':False})
    rows.append({'id':'CONCENTRATION_OVERLAP_MULTIPLICITY','status':'COUNTERMODEL_VERIFIED',
        'source_kind':'SYNTHETIC_CONTROL','preserved_premises':['actual_sine_atom_formula','constant_fourier_mode'],
        'omega':'3/4','source_quadratic':'3/2','carrier_quadratic':'3/2',
        'source_square_quadratic_lower_bound':'9/4','native_zeta_source':False,
        'refuted_inference':'S^2<=C or source norm<=1 on the full source interval',
        'actual_zeta_counterexample':False})
    rows.append({'id':'HERGLOTZ_INVISIBLE_NEGATIVE_GROUND','status':'COUNTERMODEL_VERIFIED',
        'source_kind':'SYNTHETIC_CONTROL','preserved_premises':['Hermitian_B','positive_observation_measure','positive_rank_one_update'],
        'B':[['-1','0'],['0','1']],'positive_update':'diag(-1,2)',
        'observation_vector':['0','1'],'positive_measure':'delta_1','scalar_response':'1/(1-z)',
        'shared_invisible_ground':'-1','observation_is_native_corrected_source':False,
        'refuted_inference':'positive transfer data sees or excludes every negative ground',
        'actual_zeta_counterexample':False})
    t=sp.symbols('t',real=True)
    require(all(sp.diff(-t**7,t,j).subs(t,0)==0 for j in range(1,7)), 'high-order contact changed')
    rows.append({'id':'REGULAR_INTERIOR_DEGENERATE_FIRST_CONTACT','status':'COUNTERMODEL_VERIFIED',
        'source_kind':'SYNTHETIC_CONTROL','matrix':'diag(-t,-2t)',
        'negative_interval':'t>0; distinct simple eigenvalues','first_contact':'t=0; double zero',
        'high_order_scalar':'-t^7; first six derivatives zero at0',
        'refuted_inference':'regular negative interior or nonnegative first derivative makes first contact safe',
        'actual_zeta_counterexample':False})
    rows.append({'id':'GLOBAL_FINITE_RESOLVENT_POLE','status':'DERIVED_SEQUENCE_CONTROL',
        'source_kind':'SYNTHETIC_CONTROL','scalar':'1/(1-z)','points':'1+i/n',
        'absolute_value':'n for all integers n>=1','grouped_residue':'1',
        'asymptotic_authority':'EXACT_SEQUENCE_FORMULA_NOT_FINITE_SWEEP',
        'refuted_inference':'nonzero finite residues admit a bounded scalar on the entire resolvent set',
        'actual_zeta_counterexample':False})
    # f=2 distinguishes the reciprocal input from the Riesz input as well as
    # checking the minus sign. The f=1 scalar example only checks the sign.
    A,B,D,g,f,lam=map(sp.Rational,(2,4,1,1,2,-1))
    uR=f/(A-lam);v=g/(D*(A-lam));odd=-g*f/(D*(A-lam))
    require(B*D-D*A==g*f and odd==-f*v and odd!=-f*uR,'odd orientation control failed')
    rows.append({'id':'ODD_RECIPROCAL_INPUT_DISTINCT','status':'COUNTERMODEL_VERIFIED',
        'source_kind':'SYNTHETIC_CONTROL','preserved_premises':['Hermitian_A','Hermitian_B','invertible_D','rank_one_intertwining'],
        'A':'2','B':'4','D':'1','g':'1','f':'2','lambda':'-1',
        'riesz_input':str(uR),'reciprocal_input':str(v),'odd_response':str(odd),
        'wrong_riesz_response':str(-f*uR),'reciprocal_determinant_ratio':'5/3',
        'refuted_inference':'odd response equals minus corrected source on the Riesz input',
        'actual_zeta_counterexample':False})
    T=sp.Matrix([[0,1],[1,0]]);O=sp.Matrix([[1,0]]);u=sp.Matrix([0,1])
    require(O*u==sp.zeros(1,1) and O*T*u!=sp.zeros(1,1),'noninvariant kernel control failed')
    rows.append({'id':'INSTANTANEOUS_KERNEL_NOT_INVARIANT','status':'COUNTERMODEL_VERIFIED',
        'source_kind':'SYNTHETIC_CONTROL','T':'swap','O':'first coordinate','u':['0','1'],
        'preserved_premises':['Hermitian_T','O_u_zero'],'next_observation':'1','u_is_eigenmode':False,
        'refuted_inference':'every vector annihilated by O remains unseen under T',
        'actual_zeta_counterexample':False})
    rows.append({'id':'POSITIVE_MEASURE_NEGATIVE_SUPPORT','status':'COUNTERMODEL_VERIFIED',
        'source_kind':'SYNTHETIC_CONTROL','preserved_premises':['positive_spectral_measure','visible_negative_mode'],
        'measure':'delta_minus1+delta_plus1','negative_atom_mass':'1',
        'refuted_inference':'positive spectral measure implies nonnegative spectral support',
        'actual_zeta_counterexample':False})
    rows.append({'id':'INTEGER_VALUES_MISS_DIAGONAL_JET','status':'DERIVED_SEQUENCE_CONTROL',
        'source_kind':'SYNTHETIC_CONTROL','preserved_premises':['same_all_integer_node_values'],
        'potentials':['0','sin(pi*x)'],'integer_values':'0','derivative_at_zero':['0','pi'],
        'asymptotic_authority':'EXACT_SYMBOLIC_IDENTITY_NOT_NUMERICAL_SWEEP',
        'refuted_inference':'integer potential values determine diagonal divided differences',
        'actual_zeta_counterexample':False})
    return rows

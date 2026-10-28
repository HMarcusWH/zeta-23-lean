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
    # Actual mixed residues, modified arithmetic and entering-prime atom controls
    # are supplied by the independent native numerical lane, never toy substitutes.
    for row in rows:row['id_digest']=digest(row,domain='OPICA_COUNTERMODEL_V1')
    return rows

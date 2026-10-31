"""Versioned actual-state cost/visibility campaign; frozen probes stay intact.

Unit producer: analytic Toeplitz carrier and native atom entries.
Direct checker: independently solved native basis/source plus paired Fourier
integrals. Every interval is independently refined. Finite improvement is a
research disposition, never an estimate at every aperture/cutoff or a detector
generated from an off-line zero.
"""
from __future__ import annotations
from fractions import Fraction as F
import argparse
import hashlib
import json
import os
from pathlib import Path
import sys
from . import source_evaluator as E
from .source_checker import compare_enclosures
B=E.B

HERE=Path(__file__).resolve().parent
OWN_PATHS=['research/RHRC/integration/opica_round4/source_research.py',
           'research/RHRC/integration/opica_round4/tests/test_source_research.py']


def identity():
    result=B.source_identity()
    result['research_source_sha256']={p:B.digest(B.REPO/p) for p in OWN_PATHS}
    return result


def evaluate_case(case,bits=256,representation='unit'):
    import flint
    from flint import arb,acb,arb_mat,fmpq,ctx
    B.require(representation in ('unit','direct') and bits in (256,512),'closed research numerical mode')
    before=identity();previous=ctx.prec;ctx.prec=bits
    try:
        base=B.evaluate_request(case,bits,representation,128 if representation=='unit' else 152)
        enc=base['enclosures'];K=case['K'];d=K-2;ns=list(range(-K,K+1));N=len(ns)
        def q(x):
            x=F(x);return arb(fmpq(x.numerator,x.denominator))
        def ball(x):
            lo,hi=F(x['lower']),F(x['upper'])
            return arb(fmpq(((lo+hi)/2).numerator,((lo+hi)/2).denominator),
                       fmpq(((hi-lo)/2).numerator,((hi-lo)/2).denominator))
        def matrix(rows):return arb_mat([[ball(x) for x in row] for row in rows])
        def column(rows):return arb_mat([[ball(x)] for x in rows])
        def dot(x,y):return (x.transpose()*y)[0,0]
        def norm(x):return dot(x,x).sqrt()
        def exact(x):
            m,e=x.man_exp();return F(int(m))*F(2)**int(e)
        def out(x):
            B.certain(x.is_finite(),'NONFINITE_RESEARCH_INTERVAL')
            grid=2**(96 if representation=='unit' else 128)
            lo=F((exact(x.lower())*grid).__floor__()-1,grid)
            hi=F((exact(x.upper())*grid).__ceil__()+1,grid)
            B.certain(hi-lo<=B.MAX_WIDTH,'RESEARCH_ABSOLUTE_PRECISION_BUDGET')
            return {'lower':str(lo),'upper':str(hi)}
        def zeros(A):return all(A[i,j].contains(0) for i in range(A.nrows()) for j in range(A.ncols()))
        L=ball(enc['aperture']);a=(L/(4*arb.pi()))**2
        Te=matrix(enc['physical']['even']['basis']);To=matrix(enc['physical']['odd']['basis'])
        Ge=matrix(enc['physical']['even']['gram']);Go=matrix(enc['physical']['odd']['gram'])
        A=matrix(enc['physical']['even']['operator']);Dop=matrix(enc['physical']['odd']['operator'])
        M=matrix(enc['matrix_real']);Arch=matrix(enc['components']['arch_diagonal'])+matrix(enc['components']['arch_offdiagonal'])
        f=matrix(enc['correction']['corrected_source_row']);g=column(enc['correction']['cubic_coordinate_vector'])
        _,qr,er,_=B.R3.rational_projectors(K)
        e=arb_mat([[q(x) for x in row] for row in er]);qv=arb_mat([[q(x)] for x in qr])
        pe=arb_mat([[L/(L*L+16*arb.pi()**2*n*n)] for n in ns]);ge=e*pe
        nu=dot(qv,qv);ge2=dot(ge,ge);a2=dot(qv,pe)/nu
        h=qv/nu-ge*(a2/ge2)
        B.certain(zeros(h.transpose()*M*Te-f),'RESEARCH_CORRECTED_UNCOMPRESSED_ROW_MISMATCH')
        B.certain(zeros(h.transpose()*Te),'RESEARCH_ROW_NOT_ORTHOGONAL')
        eigA=[ball(x) for x in enc['physical']['even']['eigenvalues']]
        eigB=[ball(x) for x in enc['physical']['odd']['eigenvalues']]
        ident=arb_mat([[arb(int(i==j)) for j in range(d)] for i in range(d)])
        fsharp=Ge.solve(f.transpose())
        actual_ground=bool(eigA[0]<0 and eigA[0]<eigB[0])
        lam=eigA[0] if actual_ground else arb(-1)
        B.certain(bool(lam<eigA[0] or actual_ground) and bool(lam<eigB[0]),'RESEARCH_SHIFT_OUTSIDE_DECLARED_DOMAIN')
        even=(Dop-ident*lam).solve(g)
        # Odd arithmetic uses the reciprocal source input. The Riesz-selected
        # input is retained separately; its F-value is not the odd response.
        oddlam=arb(-1)
        B.certain(bool(oddlam<eigA[0]),'ODD_RESEARCH_SHIFT_OUTSIDE_DOMAIN')
        odd=(A-ident*oddlam).solve(g)
        odd_riesz=(A-ident*oddlam).solve(fsharp)
        oddresponse=-(g.transpose()*Ge*odd_riesz)[0,0]
        B.certain((oddresponse+(f*odd)[0,0]).contains(0),'ODD_RECIPROCITY_IDENTITY_FAILED')
        tau=sum((Dop[i,i]-A[i,i] for i in range(d)),arb(0))
        even_cost=(f*Go.solve(f.transpose()))[0,0].sqrt()*(g.transpose()*Go*g)[0,0].sqrt()
        odd_cost=(g.transpose()*Ge*g)[0,0].sqrt()*(f*fsharp)[0,0].sqrt()
        source=B.R3.load_local('_opica3_research_atom',B.R3.ROUTE/'canonical_source_arb.py')
        atoms=enc['prime_power_atoms']
        options={'eval_limit':8000,'depth_limit':22,'deg_limit':96}
        tol=arb(2)**(-(bits-40))
        def integrate(fn,omega):
            z=acb.integral(lambda t,_analytic:fn(t),acb(0),acb(omega),rel_tol=tol,abs_tol=tol,**options)
            B.certain(z.is_finite() and z.imag.contains(0),'RESEARCH_FOURIER_QUADRATURE_UNRESOLVED')
            return z.real
        def fourier(v,t):
            return sum((v[j,0]*(acb(0,2*arb.pi()*n)*t).exp() for j,n in enumerate(ns)),acb(0))
        def carrier(v,omega):
            if representation=='direct':
                delta=1-omega
                return integrate(lambda t:fourier(v,-t-delta)*fourier(v,t+delta)+fourier(v,-t)*fourier(v,t),omega)
            C=arb_mat([[2*omega if n==m else (2*arb.pi()*(n-m)*omega).sin()/(arb.pi()*(n-m)) for m in ns] for n in ns])
            return dot(v,C*v)
        def mixed(hv,u,omega):
            if representation=='direct':
                delta=1-omega
                return integrate(lambda t:fourier(hv,-t-delta)*fourier(u,t)+fourier(hv,-t)*fourier(u,t+delta),omega)
            S=arb_mat([[source.q_basis(n,m,L*(1-omega),L) for m in ns] for n in ns])
            return dot(hv,S*u)
        states=[]
        for parity,coords,shift,gap,signedcost,sign in (
            ('even',even,lam,eigB[0]-lam,(even_cost+tau)/2,1),
            ('odd_reciprocal',odd,oddlam,eigA[0]-oddlam,(odd_cost-tau)/2,-1)):
            u=Te*coords;unorm=norm(u);hnorm=norm(h)
            B.certain(bool(unorm>0),'RESEARCH_ZERO_SELECTED_INPUT')
            signed_source=(f*coords)[0,0]
            arch=-dot(h,Arch*u)
            values=[];concentrated=arb(0);prime_signed=arb(0);mass=arb(0)
            for atom in atoms:
                prime=atom['q'];weight=ball(atom['weight']);omega=1-arb(prime).log()/L
                B.certain(bool(omega>0) and bool(omega<1),'RESEARCH_ATOM_COORDINATE_UNRESOLVED')
                ch,cu=carrier(h,omega),carrier(u,omega)
                pair=mixed(h,u,omega)
                B.certain(bool(ch>0 and cu>0),'RESEARCH_CARRIER_POSITIVITY_UNRESOLVED')
                bound=(ch*cu).sqrt();slack=ch*cu-pair**2
                B.certain(bool(slack>0) or slack.is_zero(),'RESEARCH_MIXED_BOUND_UNRESOLVED')
                native_pair=sum((h[i,0]*u[j,0]*source.q_basis(n,m,arb(prime).log(),L) for i,n in enumerate(ns) for j,m in enumerate(ns)),arb(0))
                B.certain((pair-native_pair).contains(0),'RESEARCH_EXCHANGE_NATIVE_PAIRING_MISMATCH')
                concentrated+=abs(weight)*bound;prime_signed+=weight*pair;mass+=abs(weight)
                values.append({'q':prime,'half_range':bool(2*arb(prime).log()>=L),
                    'omega':out(omega),'row_carrier':out(ch),'state_carrier':out(cu),
                    'signed_pairing':out(pair),'mixed_upper':out(bound),'squared_slack':out(slack)})
            residual=signed_source-(arch-prime_signed)
            B.certain(residual.contains(0),'COMPLETE_RESEARCH_SOURCE_IDENTITY_FAILED')
            global_budget=abs(arch)+2*mass*hnorm*unorm
            concentration_budget=abs(arch)+concentrated
            signed_concentration_upper=sign*arch+concentrated
            norm_trace_budget=signedcost/gap
            gain=global_budget-concentration_budget
            disposition='FINITE_GAIN' if bool(gain>0) else 'NO_OBSERVED_GAIN' if bool(gain<=0) else 'UNRESOLVED'
            signed_gain=norm_trace_budget-signed_concentration_upper
            signed_disposition='FINITE_GAIN' if bool(signed_gain>0) else 'NO_OBSERVED_GAIN' if bool(signed_gain<=0) else 'UNRESOLVED'
            # Finite CÂ¹ variation envelope: bounds the derivative entry by entry.
            # It is a cost diagnostic, not a nilsequence-class inclusion theorem.
            derivative_cost=sum((abs(h[i,0])*abs(u[j,0])*(2+4*arb.pi()*abs(n) if n==m else arb(2*(abs(n)+abs(m)))/abs(n-m))
                                 for i,n in enumerate(ns) for j,m in enumerate(ns)),arb(0))
            states.append({'parity':parity,'input_kind':('NEGATIVE_GROUND_RAY' if actual_ground else 'RESOLVENT_RAY_NOT_GROUND') if parity=='even' else 'ODD_RECIPROCAL_SOURCE_INPUT',
                'shift':out(shift),'physical_input_norm':out(unorm),'corrected_ambient_row_norm':out(hnorm),
                'source_value':out(signed_source),'actual_response':out(sign*signed_source),
                'signed_arch_part':out(sign*arch),'signed_prime_part':out(-sign*prime_signed),
                'complete_identity_residual':out(residual),'opposite_spectral_gap':out(gap),
                'global_atom_budget':out(global_budget),'concentration_budget':out(concentration_budget),
                'one_sided_concentration_upper':out(signed_concentration_upper),
                'signed_norm_trace_budget':out(norm_trace_budget),'global_minus_concentration':out(gain),
                'signed_norm_trace_minus_one_sided_concentration':out(signed_gain),
                'concentration_per_unit_input':out(concentration_budget/unorm),
                'derivative_variation_envelope':out(derivative_cost),'amplitude_envelope':out(2*hnorm*unorm),
                'cost_disposition':disposition,'signed_comparator_disposition':signed_disposition,'atoms':values})
        observation=[]
        for parity,T,G,roots,output in [('even',A,Ge,eigA,f),('odd',Dop,Go,eigB,g.transpose()*Go)]:
            negative=[(i,x) for i,x in enumerate(roots) if bool(x<0)]
            entries=[]
            for i,lam0 in negative:
                P=ident
                for j,other in enumerate(roots):
                    if j!=i:P=P*(T-ident*other)/(lam0-other)
                strength=(output*P*G.solve(output.transpose()))[0,0]
                B.certain(bool(strength>0) or strength.contains(0),'NEGATIVE_OBSERVATION_SQUARE_INVALID')
                entries.append({'eigenvalue':out(lam0),'squared_observation_strength':out(strength),
                    'status':'VISIBLE_FINITE_SIMPLE_NEGATIVE_MODE' if bool(strength>0) else 'UNRESOLVED'})
            observation.append({'parity':parity,'negative_dimension':len(negative),
                'status':'NEGATIVE_SUBSPACE_EMPTY' if not negative else 'FINITE_NEGATIVE_CHANNEL_MEASUREMENT',
                'entries':entries,'uniform_observation_bound_proved':False})
        groups=enc['spectrum']['groups'];change=arb_mat([[arb(1 if i==j else (1 if j==i+1 else 0)) for j in range(d)] for i in range(d)])
        inv=change.inv();fp=f*change;gp=inv*g
        reconstruction=[]
        for group in groups:
            P=matrix(group['projector']);difference=(fp*(inv*P*change)*gp-f*P*g)[0,0]
            B.certain(difference.contains(0),'GROUPED_BASIS_CHANGE_FAILED')
            reconstruction.append(out(difference))
        result={'schema':'OPICA4_SOURCE_RESEARCH_CASE_V1','request':case,'precision_bits':bits,'representation':representation,
            'source_kind':case['source']['kind'],'sample_kind':'SOURCE_PROBE_NOT_ZERO_GENERATED_DETECTOR',
            'states':states,'observation':observation,'joint_negative_index':sum(x['negative_dimension'] for x in observation),
            'grouped_basis_change_residuals':reconstruction,
            'odd_riesz_input_norm':out(norm(Te*odd_riesz)),'odd_response_reciprocity_residual':out(oddresponse+(f*odd)[0,0]),
            'seam_status':'EXACT_ENTERING_ATOM_ZERO_REPLAYED' if case['aperture']['kind']=='log_integer' else 'OPEN_CELL_POINT',
            'authority':'FINITE_INTERVAL_RESEARCH_ONLY','gain_is_uniform_theorem':False,
            'negative_observation_is_vacuous':all(x['status']=='NEGATIVE_SUBSPACE_EMPTY' for x in observation),
            'RH':'OPEN','Step4':'OPEN'}
        B.require(before==identity(),'research source changed during evaluation')
        return result
    finally:ctx.prec=previous


def compare(claimed,refined):
    B.require(claimed['precision_bits']==256 and claimed['representation']=='unit' and
              refined['precision_bits']==512 and refined['representation']=='direct',
              'independent research representation/precision differs')
    B.require(claimed['request']==refined['request'],'changed research request')
    # Precision/representation differ by design; all scientific quantities and
    # dispositions must independently agree, with strict interval containment.
    a={k:v for k,v in claimed.items() if k not in {'precision_bits','representation'}}
    b={k:v for k,v in refined.items() if k not in {'precision_bits','representation'}}
    return compare_enclosures(a,b,'research')


def run(output,allow_dirty=False):
    output=B.unlinked(output).absolute()
    B.require(not output.is_relative_to(B.REPO) and not output.exists(),'fresh external research output required')
    before=identity();B.require(allow_dirty or before['clean'],'clean source required for accepted research lane')
    output.mkdir(parents=True)
    report={'schema':'OPICA4_SOURCE_RESEARCH_CAMPAIGN_V1','status':'FAIL','source_identity':before,
            'authority':'INDEPENDENT_FINITE_RESEARCH_REPLAY_NOT_UNIFORM_ARITHMETIC','cases':[],'RH':'OPEN','Step4':'OPEN'}
    try:
        for case in E.prescribed_cases():
            unit=evaluate_case(case,256,'unit');direct=evaluate_case(case,512,'direct')
            count=compare(unit,direct)
            name=case['id']
            files={}
            for suffix,value in [('producer',unit),('checker',direct)]:
                (output/(name+'.'+suffix+'.json')).write_text(json.dumps(value,indent=2)+'\n',encoding='utf8')
                files[suffix]=B.digest(output/(name+'.'+suffix+'.json'))
            report['cases'].append({'id':name,'intervals_independently_contained':count,
                'files_sha256':files,
                'cost_dispositions':[s['cost_disposition'] for s in unit['states']],
                'signed_comparator_dispositions':[s['signed_comparator_disposition'] for s in unit['states']],
                'observation_dispositions':[s['status'] for s in unit['observation']],
                'source_kind':case['source']['kind']})
        B.require(before==identity(),'research source changed across campaign')
        report['status']='PASS_REPRODUCIBLE_FINITE_RESEARCH'
        return report
    finally:(output/'result.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf8')


def verify_campaign(producer,output,require_clean=True):
    """Independently rebuild every direct quantity at the current exact source."""
    producer=B.unlinked(producer).absolute();output=B.unlinked(output).absolute()
    B.require(not output.exists() and not output.is_relative_to(B.REPO),'fresh independent research output required')
    before=identity();B.require(not require_clean or before['clean'],'clean independent research source required')
    report=B.strict_json((producer/'result.json').read_bytes())
    B.require(report['schema']=='OPICA4_SOURCE_RESEARCH_CAMPAIGN_V1' and report['status']=='PASS_REPRODUCIBLE_FINITE_RESEARCH',
              'incomplete research campaign')
    B.require(report['source_identity']==before and report['RH']=='OPEN' and report['Step4']=='OPEN',
              'research campaign source or claims differ')
    B.require(report['authority']=='INDEPENDENT_FINITE_RESEARCH_REPLAY_NOT_UNIFORM_ARITHMETIC',
              'research campaign authority differs')
    cases=E.prescribed_cases()
    B.require([x['id'] for x in report['cases']]==[x['id'] for x in cases],'missing or substituted research cases')
    output.mkdir(parents=True);rows=[]
    for request,record in zip(cases,report['cases']):
        name=request['id']
        B.require(record['source_kind']==request['source']['kind'],'research summary source kind differs')
        for suffix in ('producer','checker'):
            B.require(B.digest(producer/(name+'.'+suffix+'.json'))==record['files_sha256'][suffix],
                      'research raw output hash differs')
        claimed=B.strict_json((producer/(name+'.producer.json')).read_bytes())
        supplied_checker=B.strict_json((producer/(name+'.checker.json')).read_bytes())
        B.require(claimed['request']==request,'changed native research state')
        refined=evaluate_case(request,512,'direct')
        count=compare(claimed,refined)
        # Check the submitted direct record as well as its independently rerun
        # producer comparison. Nothing is accepted from a claimed PASS flag.
        B.require(B.identical(supplied_checker,refined),'submitted direct replay differs from fresh reconstruction')
        B.require(count==record['intervals_independently_contained'] and
            record['cost_dispositions']==[s['cost_disposition'] for s in claimed['states']] and
            record['signed_comparator_dispositions']==[s['signed_comparator_disposition'] for s in claimed['states']] and
            record['observation_dispositions']==[s['status'] for s in claimed['observation']],
            'research disposition differs from raw measurements')
        (output/(name+'.json')).write_text(json.dumps(refined,indent=2)+'\n',encoding='utf8')
        rows.append({'id':name,'intervals_independently_contained':count})
    B.require(before==identity(),'source changed during independent research replay')
    result={'schema':'OPICA4_SOURCE_RESEARCH_VERIFICATION_V1','status':'PASS_INDEPENDENT_SOURCE_RESEARCH',
            'source_identity':before,'cases':rows,'uniform_estimate_proved':False,'RH':'OPEN','Step4':'OPEN'}
    (output/'result.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    return result


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--output-dir',required=True,type=Path)
    parser.add_argument('--allow-dirty-development',action='store_true');args=parser.parse_args()
    result=run(args.output_dir,args.allow_dirty_development)
    print(json.dumps({'status':result['status'],'cases':len(result['cases']),'RH':'OPEN','Step4':'OPEN'}))

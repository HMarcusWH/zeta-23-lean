"""Consistency/anti-shortcut controls, never theorem or off-line-zero evidence."""
import json
import mpmath as mp
mp.mp.dps = 60
zeta = mp.zeta
pi = mp.pi
eta = mp.mpf('0.2')
xi = 2*pi*eta
rho = mp.mpc('0.75','1')  # intentionally NOT a zero; algebra/source-only test
kappa = rho*(1-rho)
fw = lambda x: -zeta(mp.mpf('.5')+1j*x)/(mp.mpf('.5')+1j*x)
fourier_correct = fw(xi)
fourier_wrong = fw(eta)
s = mp.mpf('.5')+1j*xi
a = xi*xi+mp.mpf('.25')
psi_hat = kappa*zeta(s)/(a-kappa)
plancherel_integrand = mp.conj(fw(xi))*(1j*xi-mp.mpf('.5'))*psi_hat
stieltjes_integrand = kappa*abs(zeta(s))**2/(a-kappa)
wrong_integrand = fw(xi)*(1j*xi-mp.mpf('.5'))*psi_hat
# Generic finite-dimensional positive source: nonreal parameters are compatible
# with the resolvent/Gram identity. This is not an actual zeta-zero construction.
A = [mp.mpf('1'),mp.mpf('3')]
g = [mp.mpf('1'),mp.mpf('2')]
ks = [mp.mpc('2','1'),mp.mpc('4','-2')]
h = [[k*g0/(a0-k) for a0,g0 in zip(A,g)] for k in ks]
N = lambda i,j: sum(h[i][t]*mp.conj(h[j][t]) for t in range(2))
b = [sum(g[t]*h[i][t] for t in range(2)) for i in range(2)]
gram_residual = (ks[0]-mp.conj(ks[1]))*N(0,1) - (mp.conj(ks[1])*b[0]-ks[0]*mp.conj(b[1]))
gram_det = N(0,0)*N(1,1)-abs(N(0,1))**2
res = {
 'status':'CONSISTENCY_ONLY_NOT_FORMAL_OR_RH_EVIDENCE',
 'precision_decimal_digits':60,
 'parameter_is_not_a_zero':True,
 'fourier_wrong_2pi_mismatch':str(abs(fourier_correct-fourier_wrong)),
 'correct_conjugation_residual':str(abs(plancherel_integrand-stieltjes_integrand)),
 'missing_conjugation_mismatch':str(abs(wrong_integrand-stieltjes_integrand)),
 'reflection_same_kappa_residual':str(abs((1-rho)*rho-kappa)),
 'reflection_conjugated_kappa_mismatch':str(abs((1-rho)*rho-mp.conj(kappa))),
 'positive_gram_nonreal_control':{
   'identity_residual':str(abs(gram_residual)),
   'diagonal_norms':[str(mp.re(N(i,i))) for i in range(2)],
   'gram_determinant':str(mp.re(gram_det)),
   'source_is_synthetic_control_not_zeta':True},
 'interpretation':'Correct conventions agree; wrong scaling/conjugation/reflection fail. Positive resolvent Gram identities coexist with nonreal parameters.'
}
if not (abs(fourier_correct-fourier_wrong)>mp.mpf('.1')
        and abs(plancherel_integrand-stieltjes_integrand)<mp.mpf('1e-55')
        and abs(wrong_integrand-stieltjes_integrand)>mp.mpf('.01')
        and abs(kappa-mp.conj(kappa))>mp.mpf('.1')
        and abs(gram_residual)<mp.mpf('1e-55')
        and mp.re(gram_det)>0):
    raise RuntimeError('An expected consistency/negative control failed')
print(json.dumps(res,indent=2))

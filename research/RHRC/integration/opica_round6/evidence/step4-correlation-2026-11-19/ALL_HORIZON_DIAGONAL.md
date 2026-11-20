# An explicit starting horizon and a consequence of a contrary sign

This strengthens the [fixed sieve criterion](FIXED_SIEVE_SIGN.md) for its continuous native windows. Use the same actual \(Y=10^7\). For every integer \(n\ge 50000\) we have, independently of any zero location,
\[
 \frac1{2\log n}\int_{n-2\log n}^n E_Y(t)\,dt > 10^{72}.                 \tag{1}
\]
It follows that RH is equivalent both to the cofinal sign in the fixed sieve note and to **\(R_Y(n)<0\) for every integer \(n\ge50000\)**. These equivalences are paper deductions. The universal sign itself remains unproved.

For \(50000\le n\le 1100000\), the prime-translate bound already gives \(\int E_Y\ge (4/5)(10^{80}-1)/n\); even at the upper endpoint this exceeds \(10^{72}(2\log n)\). For larger \(n\), let \(A(x)\) count the squarefree integers \(\le x\) coprime to \(\Pi_Y\). Inserting \(\mu^2(r)=\sum_{d^2\mid r}\mu(d)\), counting the coprime integers up to \(x/d^2\) by inclusion–exclusion, and bounding the tail of \(\sum_{d>\sqrt x}d^{-2}\), gives
\[
 |A(x)-c_Y x|\le(2^{\pi(Y)}+2)\sqrt x\qquad(x\ge1).
\]
Each inner coprimality count differs from its density times the interval length by at most \(2^{\pi(Y)}\); the outer density tail costs at most \(2\sqrt x\). The leading product is exactly \(c_Y\) in (2) of the fixed sieve note.

For \(0\le u\le42000,\ X=e^{n-u}\), partial summation on \(X/n^2<r\le X\) bounds the difference between the harmonic mass of the admissible squarefree \(r\)'s and \(2c_Y\log n\) by
\[
 4(2^{664579}+2)n\,e^{-(n-42000)/2}.
\]
The right side decreases for \(n\ge1100000\), where it is less than \(e^{-60000}\). Since \(c_Y\ge1/(Y+1)\), the harmonic mass exceeds \(c_Y\log n\). Positive translation of the certified \(\int_0^{42000} V_Y^2>10^{80}-1\) into the entire native window proves (1).

Under RH the independently bounded critical and trivial contributions satisfy \(|P(t)|<10^{31}\) throughout every window considered. Therefore every such covariance is strictly negative. Conversely positivity is eventual when \(d>0\), by the merged native window theorem and the fixed diagonal limit. In particular a single rigorously established \(R_Y(n)\ge0\) at any \(n\ge50000\) would have a quantitative consequence. The verified zero-height estimate in the parent note gives \(|P(t)|<10^{31}+e^{-53890+dn}\) throughout that window. By (1), a nonnegative covariance would force
\[
 d\ge\frac{53890+\log(10^{36}-10^{31})}{n}>\frac{53972}{n}.
\]
This is a lower bound for a supremum; it does not assert the existence of a zero at the endpoint. No such nonnegative observation was obtained.

[Scalar checks](FIXED_SIEVE_CONSTANTS.json) · [Native explicit formula](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/NativeExplicitFormula.lean) · [Verified height](https://arxiv.org/abs/2004.09765)

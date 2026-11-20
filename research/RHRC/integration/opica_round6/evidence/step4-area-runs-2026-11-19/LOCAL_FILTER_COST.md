# The cost of localizing the echo at a fourth-power cut

**DERIVED on paper.** A positive observation can remove the oscillation from a hypothetical off-line zero by averaging over log time. Consider the alternative of using signed weights to do the same thing inside a much shorter interval. The functional equation and conjugation fix four shifted exponents. They impose an exact fourth-order cost on a real signed filter that cancels them all. This addresses what happens when one tries to move the negative filtered area back to the individual prime cuts.

Let \(p=\delta+i\gamma\), \(\delta,\gamma>0\), and take the orbit \(p,\bar p,-p,-\bar p\). They correspond to the nontrivial zeta-zero orbit after the shift by \(1/2\), if such an off-line zero exists. For radius \(r>0\), take all real finite signed measures \(\nu\) on \([-r,r]\) of mass 1 whose bilateral exponential transform is zero at these four points. Denote by \(V_p(r)\) the infimum of their total variations. Then, for fixed \(p\),
\[
  \lim_{r\downarrow0} r^4 V_p(r)=\frac{192}{|p|^4}.                 \tag{1}
\]
The constant measures precisely how much an arbitrary pointwise observation error can be amplified. Total variation is the dual norm for the uniform norm. An error specific to the actual prime weights can have additional signed cancellation.

## Lower bound

Reflection and averaging let us use even measures without increasing variation. Write \(m_j=\int u^j\,d\nu(u)\), so \(m_0=1\). With \(q=p^2\), we have \(\Im q=2\delta\gamma\ne0\). Cancellation of the orbit gives
\[
 0=\int\cosh(pu)\,d\nu
   =1+\tfrac12 q\,m_2+\tfrac1{24}q^2m_4+O_p(r^6\|\nu\|_{\rm TV}).
\]
For proving a lower asymptotic constant it suffices to consider sequences with \(r^4\|\nu\|_{\rm TV}\) bounded. For such sequences the error is \(O_p(r^2)\). Taking real and imaginary parts is an invertible real system for \(m_2,m_4\). The functional \(z\mapsto\Re z-(\Re q/\Im q)\Im z\) has values \(1,0,-|q|^2\) on \(1,q,q^2\), respectively. It follows that \(m_4=24/|p|^4+O_p(r^2)\), \(m_2=O_p(1)\), with constants also depending on the chosen bound on \(r^4\|\nu\|_{\rm TV}\).

The quartic Chebyshev polynomial \(T_4(v)=8v^4-8v^2+1\) is bounded by 1 in absolute value on \([-1,1]\). Hence
\[
 r^4\|\nu\|_{\rm TV}\ \ge\ |8m_4-8r^2m_2+r^4|
   \ \longrightarrow\ 192/|p|^4
\]
on every such sequence on the right. This proves the lower limit inequality.

## A matching real filter with five observation times

Use symmetric atoms on \(\{\pm r,\pm r/\sqrt2,0\}\) with total masses \(a,b,c\) on the respective classes and \(c=1-a-b\). Write \(s=m_2, v=m_4\); then
\[
 a=2v/r^4-s/r^2,\qquad b=4s/r^2-4v/r^4.
\]
The exact equation is \(1+a[\cosh(pr)-1]+b[\cosh(pr/\sqrt2)-1]=0\). After the displayed substitution the coefficients of \(s,v\) tend to \(q/2,q^2/24\). The two real equations are nonsingular for all sufficiently small \(r\) since the limiting determinant is \(|q|^2\Im q/48\ne0\). Their exact solutions converge, with \(v\to24/|p|^4\). Therefore
\[
 r^4(a,b,c)\to(48,-96,48)/|p|^4 .
\]
This furnishes an admissible filter with the upper limit in (1). Symmetry and reality kill all four exponents, including the reflected pair. A probability measure is already impossible when \(2\gamma r<\pi\), since all tilted phases lie in an open semicircle.

## What it costs on the actual grid

Near \(x=M^4\), a block of \(M^{1-\eta}\) consecutive indices spans log radius of order \(M^{-\eta}\), for fixed \(0<\eta<1\). A local unit-mass signed filter that cancels even one complete off-line quartet there has uniform error amplification of order at least \(M^{4\eta}\) for that fixed quartet. Equivalently its log cost grows at least \(\eta\log x+O_p(1)\). The model allows arbitrary finite measures on the interval, so restricting the observation times to actual grid points cannot improve the lower bound. The five-node upper bound concerns the continuous interval only. The argument does not assert that an off-line zero exists or that every method of treating the actual primes must pay the total-variation norm.

This reveals a specific missing input in the graph's recovery theorem. That theorem assumes a subexponential budget separately for the observation norm and the errors. Kernel vanishing proves cancellation of a mode; it supplies neither budget. Even in a norm too large for that theorem, the *product applied to the actual signed error vector* could still be small. Proving such a bound from the arithmetic, or an independent power saving on positive runs of the genuine prime area, would advance Step 4. [Recovery theorem](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/OPICAFollowup/JointObservation.lean#L200) · [Actual zero and multiplicity theorem](https://github.com/HMarcusWH/zeta-23-lean/blob/c867a8f15320ad6ac69177e0a498de4cb9d744f9/Zeta23/ExceptionalZero/NativeActualKernelZeroJets.lean#L42)

## Applying the five observations to the actual primes

The exact input to the signed filter can be computed without expanding any zero. Put \(y_i=xe^{u_i}\), \(h_i=y_i-x\), \(|u_i|\le r\), with signed masses \(w_i\). Define the genuine triangular prime sum
\[
 B_i=\begin{cases}
 \sum_{x<p\le y_i}(y_i-p)\log p,&h_i\ge0,\\
 \sum_{y_i<p\le x}(p-y_i)\log p,&h_i<0 .
 \end{cases}
\]
The asymmetric boundary at \(x\) pays for a possible prime at the center. For \(A(x)=\int_2^x(\vartheta(v)-v)dv\), the exact observed value is
\[
 \sum_i w_i\,\frac{A(y_i)}{y_i^{3/2}}
 =
 \sum_i \frac{w_i}{y_i^{3/2}}\left[A(x)+h_i(\vartheta(x)-x)\right]
 +\sum_i \frac{w_i}{y_i^{3/2}}(B_i-h_i^2/2).
\]
The previously established short-interval result bounds each last parenthesis by \(O(h_i^2 e^{-(\log x)^{1/4}/4}+x^{4/3}\log x)\) uniformly when \(|h_i|\le x/100\). Applying the triangle inequality with the five optimized weights gives \(O_p(x^{1/2}r^{-2}e^{-(\log x)^{1/4}/4}+x^{-1/6}r^{-4}\log x)\). The first allowance already exceeds a constant at any polynomially small \(r\). The expression whose sign or cancellation could improve this loss is now explicit. [Source and derivation of the local bound](../step4-strip-2026-11-19/ACTUAL_PRIME_AVERAGING_ERROR.md)

The finite calculation evaluated both sides independently at nine combinations of center and radius, using the illustrative quartet generated by \(p=0.2+17i\). At center 3,000 the signed local remainder was about \(+1.87\) at radius 0.02 and \(-13.99\) at radius 0.01. The point values came from complete ordinary-prime prefix sums; the local calculation enumerated each prime–cut incidence. The filter parameter was synthetic. This sign reversal rules out imposing a constant sign on this finite statistic for arbitrary filter choices. Its size on late, arithmetically selected windows remains open. [Code](check_echo.py) · [Numerical results](ECHO_CONTROLS.json)

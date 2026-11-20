# Signed gcd correction for the deterministic largest-prime cone

**DERIVED on paper.** Fix \(0<\kappa<.01\), \(Z=X^\kappa\), and \(B=\sup_\rho\Re\rho\). In the genuine all-rough graph at the native integer cutoff \(X\), the complete signed large-gcd contribution incident to any nonzero \(n\) with \(n/P^+(n)\le Z\) is
\[
  O_{\kappa,\epsilon}\bigl(X^\epsilon Z^{2B-1}\bigr).
\]
This estimate holds at every large cutoff, including clipped shells and cells. It pays the entire correction from the gcd mask on those rows. It leaves their unmasked incident covariance to be determined. [Graph and weighted counts](../step4-harmonic-recovery-2026-11-19/DYADIC_TREE.md) · [Uniform restricted Mertens estimate](ROUGH_PRIME_TRANSPORT.md)

## Exact fibre

Let \(q=pa\) be a cone row in the shell \([U,2U)\), so \(p=P^+(q)\ge U/Z\). Let \(r\ne q\) belong to the same clipped tree node \(J\). If \(p\nmid r\), then \(\gcd(q,r)\mid a\le Z<X^{.01}\). Otherwise \(r=pc\), with \(c\le2Z<p\) in every terminal shell for large \(X\). Hence the gcd test fails and \(p\) is also the unique largest prime of \(r\). This gives a disjoint parametrization of **every** failed incident pair, including those where only one endpoint lies in the cone. Every prime in this parametrization exceeds the roughness cutoff \(y=(\log X)^{2+o(1)}\).

Write \(\mu_y(c)=\mu(c)\mathbf1_{P^-(c)>y}\), including \(\mu_y(1)=1\). Define
\[
  I_p=\{c\ge1:pc\in J\},\quad
  V_p=\sum_{c\in I_p}\mu_y(c),\qquad V_p^>=\sum_{c\in I_p,\ c>Z}\mu_y(c).
\]
Both are signed sums over single intervals, even at a clipped boundary. For \(p\ge U/Z\) the product of the two original signs equals the product of the two cofactor signs. The exact ordered off-diagonal correction in \(J\) before its weight is
\[
  \sum_{U/Z\le p\le2U}
  \left\{V_p^2-(V_p^>)^2-\sum_{\substack{c\in I_p\\c\le Z}}\mu_y(c)^2\right\},
\]
where the outer sum is over primes. The diagonal subtraction involves only cone rows, each with its unique largest prime. Its weighted total is \(O(\log X)\).

## Lower-scale price

For each fixed \(\eta>0\), the restricted Mertens estimate gives
\[
   |V_p|+|V_p^>|\ll_\eta X^{o_\eta(1)}(2U/p)^{B+\eta}.
\]
It follows by taking two prefix differences and removing the small Euler factors from the unrestricted Mertens bound. The product of the removal costs is subpower for this \(y\). When \(B=1\) direct counting also suffices. After paying the shell factor \(1/U\), the absolute value of the sum of square differences is at most
\[
  X^{o_\eta(1)}U^{-1}\sum_{U/Z\le m\le 2U}(2U/m)^{2B+2\eta}
     \ll_\eta X^{o_\eta(1)} Z^{\,2B-1+2\eta}.
\]
The last inequality follows by comparison with the integral from \(U/Z-1\) upwards; \(2B+2\eta>1\), including the endpoint \(B=1/2\). The improvement comes from summing the two signed squares before taking absolute values inside them. The sum of the remaining level weights \(2^{-k}\) over all nodes of the native tree is \(X^{o(1)}\). Choosing \(\eta\) after \(\epsilon\) proves the stated bound.

More generally the same argument works for a deterministic union of \(X^{o(1)}\) cofactor intervals up to \(Z\), even if their endpoints depend on the prime \(p\). The complement inside \(I_p\) then has at most \(X^{o(1)}\) interval components. Triangle inequality on the signed interval sums incurs only a subpower. The same statement holds for bounded-variation cofactor weights in the analogous weighted quadratic by partial summation. A selector that splits by cofactor sign need not satisfy either hypothesis.

## Consequence for the remaining graph

Let \(A(E)=\sum_Jw_J(\sum_{n\in E\cap J}\mu_y(n))^2\) and let \(R\) denote the deterministic cone complement. Write \(D(E)\) for the total ordered, distinct signed correction at \(\gcd(q,r)\ge X^{.01}\), and let \(C(E)\) keep only the native primitive pairs. Then
\[
 C(R)=A(R)-D(R)+O(\log X),\qquad
 D(R)=D(\mathrm{all})+O_\epsilon(X^\epsilon Z^{2B-1}).
\]
For \(B>1/2\) the existing rough graph result bounds \(D(\mathrm{all})\) by \(O_\epsilon(X^{(1-.01)(2B-1)+\epsilon})\). Thus all the large-gcd corrections in the deterministic complement are below the leading exponent. In particular, if the cone energy exceeds the full energy by a power on a sequence of cutoffs, then the complement also carries that larger energy there, by \(\sqrt{A(R)}\ge\sqrt{A(\mathrm{cone})}-\sqrt{A(\mathrm{all})}\). Conversely, if the cone energy is smaller by a power, the complement retains the full exponent. A cone of comparable size whose node charges align with the full input remains possible from these inequalities alone.

The unmasked incident form is \(A(\mathrm{all})-A(R)\) after the diagonal is paid. In each node it contains correlations between **different** large primes. The fibre estimate controls equal-prime pairs only. Its above application to interval-defined cofactor selections does not transfer to the adaptive semiprime partners from greedy matching: restricting a cofactor interval to a chosen Möbius sign can give a sum of the size of its cardinality. A separate prime-density calculation establishes the actual deterministic cone and complementary covariances both have exponent one, independently of RH. The source-balanced partner problem and Step 4 remain **OPEN**. [Unconditional shell drift and mask calculation](CONE_DRIFT.md)

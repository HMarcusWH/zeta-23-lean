# What the GCD test removes from the fixed-cofactor retirement

**DERIVED on paper.** I checked the mask restoration in [the positive-density retirement](POSITIVE_DENSITY_RETIREMENT.md), including edges joining two retired vertices and edges joining a retired vertex to any surviving vertex. An absolute bound of order \(2^{-s}X^\alpha\) per shell holds. When the mandatory cofactor exponent \(\kappa>0\) is fixed, actual positive pairs already force an absolute cost of order at least \(2^{-s}X^\kappa/\log^3 X\). The signed cost still allows cancellation.

## Uniform upper and genuine absolute lower

Take the original rough squarefree labels, \(X=2^{100t}\), \(D=X^{.01}\), \(y=(\log_2 X)^2\), and one full terminal shell \(U\le n<2U\). A node of integer length \(H\) has weight \(H/(UH_0)\), where \(H_0=U2^{-s}\). For each selected \(n=mp\), \(p=P^+(n)\), \(m\le X^\alpha<D\), and \(p\ge U/X^\alpha>D\). A distinct vertex \(r\) fails the mask exactly when \(p\mid r\). The number of distinct possible \(r\) in the same node is at most \(2\lfloor(H-1)/p\rfloor\). The bound holds also when \(p>H\). Geometric summation gives a cost \(O(H_0/(Up))\) per selected endpoint in one orientation. Allowing both orientations and summing over at most \(U\) endpoints gives \(O(2^{-s}X^\alpha)\). This works for any selector within the stated support. In fact summing over cofactors first, the ordinary prime count in \([U/m,2U/m]\) is \(O(U/(m\log U))\) uniformly in \(m\le X^\alpha\). Each \(1/p\le m/U\), giving \(O(2^{-s}X^\alpha/\log U)\) for the same absolute mass.

For the lower bound let \(M=\lfloor X^\kappa/2\rfloor\) and take all primes \(p\in[1.1U/M,1.15U/M]\). For each, take all primes \(m\in[M,1.1M]\). For fixed \(0<\kappa<.01\) and sufficiently large \(X\), all these semiprimes are genuine mandatory rough positive vertices in \([1.1U,1.265U]\). There are \(R\gg M/\log M\) choices of cofactor by the prime number theorem. Split the products for this one \(p\) among the \(2^s\) base cells, with counts \(r_J\). Convexity gives at least \(R^2/2^s-R\gg R^2/2^s\) ordered distinct pairs within a shared cell. Every pair has exact gcd \(p\ge D\), and every weight is \(1/U\). The prime number theorem gives \(\gg U/(M\log U)\) choices of \(p\), with disjoint pairs. Consequently
\[
  \text{absolute excluded incidence in this shell}
  \gg_\kappa \frac{X^\kappa}{2^s(\log U)(\log M)^2}.
\]
This lower applies to every selection containing all mandatory vertices and to any set of depths containing the base. For the mandatory vertices alone the exponent of their absolute incident cost is exactly \(\kappa+o(1)\), by the upper with \(\alpha=\kappa\). The test does not give a corresponding lower for the signed sum.

## Exact signed decomposition and the smaller mandatory error

For each distinguished large prime \(p\) of a selected endpoint, the vertices divisible by \(p\) form a fibre. Every label in the shell belongs to at most one such fibre since \((U/X^\alpha)^2>2U\). In each original node \(J\), write \(A_{p,J}\) and \(R_{p,J}\) for the full and surviving sign sums over multiples of \(p\). Write \(N_{p,J}\) for the number of selected multiples of \(p\). The exact excluded signed *ordered* off-diagonal incidence is
\[
  \sum_J \frac{|J|}{UH_0}\sum_p (A_{p,J}^2-R_{p,J}^2-N_{p,J}).
\]
Each contributing pair appears in exactly one fibre for that node. This formula retains every complement and subtracts precisely the selected diagonals.

For mandatory vertices alone there is a stronger signed estimate uniform through all depths. Set \(Z=X^\kappa\), \(B=\sup_\rho\Re\rho\), \(b=B-1/2\). Relevant primes satisfy \(p\ge U/Z\). In a band \(V\le p<2V\), put \(T=2U/V\), so \(1\le T\ll Z\). Within a single node every rough multiple is \(p m\) with \(m\ll T<p\), and has sign \(-\mu(m)\). The full cofactors form an interval of integers and the surviving cofactors form its intersection with \(m>Z\). For each of the two signed sums use the uniform rough Mertens estimate (3) from [the original source comparison](ROUGH_PRIME_TRANSPORT.md), by subtracting prefixes. Its bound is \(O_\eta(X^{o_\eta(1)}T^{B+\eta})\). There are \(O(U/T)\) possible primes in the band, at most \(U/H\) nodes at each depth, and the weight is \(H/(UH_0)\). After multiplying these factors the two sums of squares contribute
\[
 O_\eta\!\left(2^s X^{o_\eta(1)}T^{2b+2\eta}\right).
\]
The selected diagonals cost \(O(1)\) per shell after geometric summation. Summing the bands, depths and shells and taking arbitrarily small fixed \(\eta>0\) bounds the complete signed mask error incident to the mandatory vertices by \(X^{2\kappa b+o(1)}\). This is below \(X^{2b}\) when \(b>0\), and subpower if \(b=0\). It controls the effect of applying the GCD restriction to their incident edges. The unmasked matched retirement separately uses selected opposite-sign partners. For that larger selection, their removal cuts holes in the remaining cofactor interval. The same interval subtraction does not bound its \(R_{p,J}^2\). The preceding absolute upper still covers this case for each requested tolerance with \(\alpha\) fixed sufficiently small.

## One literal excluded edge

At \(X=2^{1399600}\), use \(p=2^{1398269}-1\), \(m_1=2^{1279}-157\), \(m_2=2^{1279}-1\). The large prime has an independently verified GIMPS primality result. A local proof-mode FLINT test established primality of both cofactors. Both \(p m_i\) are positive mandatory rough labels at \(\kappa=1/1000\). Their exact gcd is \(p\). They share the last base cell of the shell \(U=2^{1399547}\) and its subsequent 86 dyadic descendants before separating. The ordering-symmetric signed base contribution removed by the mask is exactly \(2/U\). This finite control tests the native geometry and GCD predicate. It does not evaluate the whole covariance or any prime-short-interval matching threshold. [GIMPS source](https://www.mersenne.org/primes/?press=M1398269) · [FLINT primality guarantee](https://flintlib.org/doc/fmpz/fmpz_is_prime.html) · [reproducible script](check_native_mask_collision.py) · [small receipt](NATIVE_MASK_COLLISION.json)

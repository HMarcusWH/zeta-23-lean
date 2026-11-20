# Two nonnegative graph calculations isolate the signed error

**DERIVED on paper.** Fix \(0<\kappa<.01\), for example \(1/1000\). The following two rational statistics on the actual arithmetic tree, computable at every integer cutoff, jointly carry the exact growth exponent of the remaining Step 4 estimate. The first measures the mismatch in the energies of two disjoint groups of vertices. The second sums squares of the mismatches between their signed charges across pairs of nodes. Neither test requires finding a zeta zero, choosing partners, or taking a square root.

## Quantities and exact factorization

Use the original dyadic grid, its positive ordered weights \(w_J\), terminal interval, and rough Möbius signs from [the rough-source result](ROUGH_PRIME_TRANSPORT.md). Keep every coarse node (or all nodes, consistently). Put a vertex in the first set when \(n/P^+(n)\le X^\kappa\), and in the second otherwise. Let \(l_J,h_J\) be the two signed integer charges in node \(J\). Use
\[
 A=\sum_Jw_J l_J^2,\quad B_0=\sum_Jw_J h_J^2,\quad g=\sum_Jw_J l_J h_J.
\]
The Gram matrix here is the full positive node form **before** subtracting the diagonal and the bad-GCD pairs. Neither of those subtractions is inserted inside a determinant. Their existing signed bounds reconnect this positive form to the native primitive covariance below.

Define
\[
 d_1=(A-B_0)^2,\qquad
 d_2=4(AB_0-g^2)=4\sum_{I<J}w_Iw_J(l_Ih_J-l_Jh_I)^2 .
\]
The last identity follows by expanding the squares and exchanging the ordered pair of nodes. Put \(E_\pm=\sum_J w_J(l_J\pm h_J)^2\). Exact finite multiplication gives
\[
 d_1+d_2=E_+E_-,\qquad d_1,d_2\ge0.
 \tag{1}
\]

## Why the denominator has a known arithmetic size

Write \(P_y=\prod_{p\le y}(1-1/p)^{-1}\), \(y=\lceil\log_2 X\rceil^2\). In a whole terminal shell \(U\asymp X\), the first set has signed charge \((1+o(1))P_y U/\log^2 U\) and the second the opposite main term. Thus at the \(2^s\) base cells of that shell, Cauchy gives
\[
 E_-\gg X\,2^{-s}P_y^2/\log^4 X=X^{1-o(1)} .
\]
Every original integer horizon has such a shell eventually. The unsigned tree bound gives \(E_-=O(X+\log X)\), so \(E_-=X^{1+o(1)}\) on **every** sufficiently late cutoff. This conclusion uses the nonzero derivative of \(1/\zeta\) at 1 in the prime-density calculation. For an arbitrary partition of the vertices the denominator can vanish. [Signed arithmetic main term and its full complement](CONE_DRIFT.md)

Let \(b=\sup_\rho\Re\rho-1/2\). The full rough-source result gives \(1+E_+=X^{2b+o(1)}\). Indeed the difference from the actual primitive covariance consists of the diagonal \(O(\log X)\) and the entire signed bad-GCD contribution \(O_\epsilon(X^{(1-.01)2b+\epsilon})\) for \(b>0\), subpower for \(b=0\). These are strict power savings relative to the putative leading exponent when \(b>0\). Nothing is asserted about mask costs after splitting the arithmetic into arbitrary sign classes. Substitution in (1) gives the arithmetic law
\[
 \boxed{\displaystyle
 1+\frac{d_1(X)+d_2(X)}{X}=X^{\,2b+o(1)}.}
 \tag{2}
\]
For \(b=0\) the upper and the added one suffice; no lower on the unnormalized \(E_+\) is needed. By nonnegativity one can replace the sum by the maximum at constant cost. In particular it suffices to prove, for every \(\epsilon>0\), at arbitrarily large **common** horizons,
\[
 |A-B_0|\le X^{1/2+\epsilon},\qquad
 \sum_{I<J}w_Iw_J(l_Ih_J-l_Jh_I)^2\le X^{1+\epsilon}.
 \tag{3}
\]
Conversely (3), at every sufficiently late horizon with each requested exponent, follows from \(b=0\). Preliminary exponents can be halved to absorb squaring and absolute constants. The first estimate concerns radial error. The second concerns the failure of signed charges to be proportional across different nodes.

## How accurately the two sectors already compensate

Let \(F(v)=v^{3/5}(\log v)^{-1/5}\). Unconditionally \(E_+\ll X\exp(-cF(\log X))\) for some \(c>0\). To verify uniformity for this rough source, use \(\mu_y=\mu*\mathbf 1_{\text{\(y\)-smooth}}\). In a prefix \(T\asymp U\), the terms with smooth multiplier \(d\le\sqrt T\) contribute \(O(TP_y e^{-cF(\log X)})\) by the unconditional Mertens bound. For \(d>\sqrt T\), counting and Rankin's bound on reciprocals give \(O(T(\log y)^C\exp(-\log T/(2\log y)))\). Node charges are differences of two such prefixes. The sum of node weights per shell costs \(O(2^s\log X/U)\); \(s=O(\sqrt{\log X})=o(F(\log X))\). This proves the energy estimate on the whole tree, including clipped nodes. [Lee and Leong, Mertens estimate](https://arxiv.org/abs/2208.06141) · [Original weighted-node calculation](../step4-harmonic-recovery-2026-11-19/SIGNED_COMPENSATION.md)

Both \(A\) and \(B_0\) exceed \(c'X2^{-s}P_y^2/\log^4 X\) by the same whole-shell argument. Hence for the signed node vectors and their uncentered angle \(\theta\), for some \(c''>0\),
\[
 0\le 1+\cos\theta\le E_+/(2\sqrt{AB_0})
       \ll \exp(-c''F(\log X)).
\]
Also \((\sqrt A-\sqrt{B_0})^2\le E_+\). These are genuine estimates of joint compensation, but their rate is insufficient for (3). For example a relative angular error \(e^{-cF(\log X)}\) can coexist with energy of any fixed positive power smaller than one. A finite near-perfect angle can also coexist with a large length mismatch.

The same formulas and bounds apply to the [matched reduction](SPARSE_COMPENSATION.md) along its aligned cutoffs: use the surviving subset of the first sector for \(l_J\) and the same untouched second sector. All first-sector charges on base cells are preserved exactly. The unmasked positive energy \(E_+\) on survivors changes by \(O(\log X)\) by the intermediate-level matching estimate and the diagonal budget. The full native masked comparison on this single reduced graph is recorded in that proof.

## Exact finite falsification check

At \(X=2^{20}\), the native threshold gives \(y=400\) and \(\lfloor X^{1/1000}\rfloor=1\). Among the genuine rough labels the first sector consists of 9,800 primes, the second of 2,515 semiprimes. The native masked mixed term is exactly \(-3966543289/268435456\), and the complete masked sum is \(4284298445/268435456\). In the node Gram matrix, \(\cos^2\theta=503470901232350000672/504770307773977362387\), approximately .99743, with negative cross term. Yet \(d_1\) is about 730.2 and \(d_2\) about .56. A test using only aligned directions would largely miss the energy mismatch here. At \(X=2^{16}\) one sector is empty, so its angle is undefined and the rational statistics remain well defined. The node calculation uses exact integers and dyadic weights; direct pair enumeration independently checks both smaller cutoffs. These runs cover the deterministic partition only and make no asymptotic claim. [Calculation](check_signed_gram.py) · [Rational receipts](SIGNED_GRAM_CHECK.json)

**OPEN.** No independent upper of the strength (3) was obtained for both quantities on common arbitrarily late cutoffs. A good bound on their angle alone cannot supply the first estimate. The equality (2) identifies where an off-line zero would be visible without attributing a finite observation to any particular zero.

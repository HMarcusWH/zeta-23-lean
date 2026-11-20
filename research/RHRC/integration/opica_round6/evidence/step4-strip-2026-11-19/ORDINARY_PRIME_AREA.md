# Transferring a signed bound to the full ordinary-prime history

**DERIVED, with explicit finite arithmetic.** Let \(\vartheta(x)=\sum_{p\le x}\log p\), \(A_\vartheta(x)=\int_2^x(\vartheta(t)-t)\,dt\), and \(A_\pi(x)=\int_2^x(\pi(t)-\operatorname{li}(t))\,dt\). A negative upper for \(A_\vartheta\) on a full prefix gives a negative upper for \(A_\pi\) on that same prefix once its terminal margin exceeds an explicit \(O(x)\) term. Every ordinary prime retains its original position and its full history. The proper powers that enter the proof of the bound for \(A_\vartheta\) are accounted for before this transfer.

For \(2\le t\le x\) put
\[
 c_0=2/\log 2-\operatorname{li}(2),\qquad
 K_x(t)=\frac1{\log t}+\frac{x-t}{t\log^2 t}.
\]
Stieltjes partial summation, including the prime \(2\), gives the following identities for all real \(x\ge2\):
\[
\begin{aligned}
\pi(x)-\operatorname{li}(x)
 &=c_0+\frac{\vartheta(x)-x}{\log x}
     +\int_2^x\frac{\vartheta(t)-t}{t\log^2t}\,dt,\\
A_\pi(x)
 &=c_0(x-2)+\frac{A_\vartheta(x)}{\log x}
       +\int_2^x(-K'_x(t))A_\vartheta(t)\,dt,\\
-K'_x(t)&=\frac{1}{t\log^2t}
       +\frac{x}{t^2\log^2t}
       +\frac{2(x-t)}{t^2\log^3t}>0.
\end{aligned}
\]
To obtain the second line integrate the first on the compact prefix and exchange the finite integrals. The resulting kernel against \(A_\vartheta'(t)\) is \(K_x(t)\); integrate by parts and use \(A_\vartheta(2)=0\). Thus a nonpositive \(A_\vartheta\) on \([2,x]\) implies
\[
 A_\pi(x)\le c_0(x-2)+A_\vartheta(x)/\log x.          \tag{1}
\]
The endpoint constant is essential. Under the normalization \(\operatorname{li}(x)=\operatorname{Ei}(\log x)\), \(0<c_0<3\), directly from that function's convergent series at \(\log 2\) (also checked with Arb). The kernel has the same sign on the entire prefix.

In particular, if \(A_\vartheta(u)<-0.17u^{3/2}\) for \(10^{19}\le u\le X\), together with \(A_\vartheta(u)\le0\) for \(2\le u\le10^{19}\), then
\[
 A_\pi(u)<-0.16\,u^{3/2}/\log u \qquad(10^{19}\le u\le X).
\]
Indeed \(3\log u/\sqrt u<0.01\) there by monotonicity and its value at \(10^{19}\). On \(2<u\le10^{19}\), the published pointwise \(\pi(t)<\operatorname{li}(t)\) gives \(A_\pi(u)<0\) directly. The same early-range comparison for \(\vartheta(t)-t\) gives the required prefix for (1). [Johnston, Lemma 2.1](https://arxiv.org/pdf/2201.06184#page=2)

The [additive-averaging verification](ADDITIVE_PRIME_AREA.md) supplies \(X=10^{46}\) for this implication. The separate [band-limited computation](BANDLIMITED_THETA.md) gives \(A_\vartheta(u)<-0.056u^{3/2}\) through \(10^{48}\), and \(A_\vartheta(u)<-0.002u^{3/2}\) through \(1.21\cdot10^{48}\), in both cases starting at \(10^{19}\). Since \(3\log u/\sqrt u<0.001\) from \(10^{19}\) onwards, (1) gives
\[
 A_\pi(u)<-0.055\,u^{3/2}/\log u\quad (10^{19}\le u\le10^{48}),\qquad
 A_\pi(u)<-0.001\,u^{3/2}/\log u\quad (10^{19}\le u\le1.21\cdot10^{48}).
\]
Thus both signed areas are negative at **every real \(2<u\le1.21\cdot10^{48}\)**. The result for the integral permits its derivative \(\pi(u)-\operatorname{li}(u)\) to take either sign. The [reproducible finite checks](ORDINARY_AREA_CHECK.json) include the endpoint constant, the fourth roots of the claimed ceilings, and direct comparison of the two sides of the Abel identity using rigorous prime-by-prime integration. An independent continuation to unbounded scales with the coverage in [the sign-run criterion](COUNT_SAVING_SCOPE.md) remains open.

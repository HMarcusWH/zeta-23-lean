# The actual packet's Fourier-input approximation survives the full prime-operator cost

10 November 2026. **DERIVED paper estimate; not a new compiled theorem.** This pays one approximation cost in the newly identified source-column bridge. It does not prove a source-response upper, identify a ground vector, or complete the finite moment-slice interface.

## Exact scope

Let h be the original correlation source, supported in [-S,S]. For L>2S put f_L(t)=h(t-L/2) on [0,L]. Let Q_K be the ordinary orthogonal Fourier projection onto the modes |n|<=K, with frequency 2*pi*n/L. This is the full finite Fourier space, not the narrower pole-neutral or endpoint-moment slice.

The actual complete physical prime operator is

\[
(P_L f)(t)=\sum_{2\le n\le e^L}\frac{\Lambda(n)}{\sqrt n}
\big[f(t-\log n)+f(t+\log n)\big],
\]

with zero extension and every prime power retained. The source-column identity derived in the companion note is

\[
P_L f_L(t)=Z(|t-L/2|).
\]

## 1. Inherited source smoothness is quantitative enough

The current [UniversalSincPhysicalBounds](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/CCM/UniversalSincPhysicalBounds.lean) proves, for the literal q and fixed scale, constants C,A>0 with

\[
\|q^{(m)}\|_\infty\le C A^m(m!)^2
\]

for all m. This is derived there from actual Fourier-product moments, not assumed for an arbitrary source. Since q is a probability density and

\[
h=(q*q)^{(4)}-\tfrac12(q*q)''+\tfrac1{16}(q*q),
\]

differentiation under compact convolution and absorption of the fixed factorial shifts give constants C_h,A_h>0 such that

\[
\|h^{(m)}\|_2\le C_h A_h^m(m!)^2\quad(m\ge0).
\tag{1}
\]

All constants are independent of L,K and m. For the absorption, (m+j)!/m! is a fixed-degree polynomial for j<=4, whose square is bounded by a fixed constant times a fixed exponential in m. No growing derivative order is charged without its factorial cost.

## 2. Exact Fourier tail estimate

The centered packet and all its derivatives vanish at both endpoints of [0,L]. Thus periodic integration by parts introduces no boundary terms. Parseval gives, for every nonnegative integer m,

\[
\|(I-Q_K)f_L\|_2
\le \left(\frac{L}{2\pi(K+1)}\right)^m\|h^{(m)}\|_2
\le C_h\left(\frac{A_h L}{2\pi(K+1)}\right)^m(m!)^2.
\tag{2}
\]

Put X=2*pi*(K+1)/(A_h L). If X>=16, choose m=floor(sqrt(X)/2). Then m>=sqrt(X)/4 and m!<=m^m. The right side of (2) is at most

\[
C_h(m^2/X)^m\le C_h4^{-m}
\le C_h\exp\big(-\tfrac14\log(4)\sqrt X\big).
\]

Consequently fixed source constants C',c'>0 give

\[
\|(I-Q_K)f_L\|_2\le C'\exp(-c'\sqrt{K/L})
\tag{3}
\]

whenever K/L is sufficiently large. At the quartic cutoff K=ceil(L^4), this is at most C' exp(-c' L^(3/2)). The choice of derivative order is now justified by the actual Gevrey bound (1), unlike an unsupported use of C-infinity regularity alone.

## 3. Pay the complete arithmetic operator amplification

Each zero-extended shift is an L2 contraction. The elementary inequality Lambda(n)<=log(n) and sum_(n<=N) n^(-1/2)<=2sqrt(N) give, for L>0,

\[
\|P_L\|_{2\to2}\le2\sum_{2\le n\le e^L}\frac{\Lambda(n)}{\sqrt n}
\le4L e^{L/2}.
\tag{4}
\]

Combining (3)–(4), at the quartic cutoff,

\[
\boxed{\|P_L f_L-P_LQ_K f_L\|_2
\le4C' L\exp(L/2-c'L^{3/2}).}
\tag{5}
\]

For each fixed B>0, the right side is smaller than exp(-B L) once L exceeds a source- and B-dependent threshold fixed in advance. Thus replacing the input packet by its finite Fourier projection is compatible with the complete arithmetic operator. No unsigned estimate of the response itself is inferred from (4); that estimate is used only to amplify an independently tiny approximation error.

This is also enough for the selected weighted L1 error. On [0,L], define Omega_L(t)=exp(-(L/2-|t-L/2|)/2). Its squared L2 norm is 2(1-exp(-L/2))<=2. Cauchy gives

\[
\left|\int_0^L\Omega_L|P_Lf_L|-\int_0^L\Omega_L|P_LQ_Kf_L|\right|
\le\sqrt2\,\|P_L(f_L-Q_Kf_L)\|_2.
\tag{6}
\]

The first integral is exactly 2A_Z(L/2). Hence (5) pays this *input replacement* at an error smaller than every fixed exponential, while retaining the full output.

## 4. What has not been paid

Q_K f_L is not automatically a member of the finite native moment slice. The actual source's continuum moments are exact, but the truncated Fourier packet can have small nonzero endpoint or pole moments. The subsequent paper result `INPUT_MOMENT_CORRECTION.md` now supplies an explicit four-node correction, pays its norm and arithmetic amplification, and constructs a member of the exact even slice. This is a separate derived input result; it does not change the full-output limitation below.

More importantly, (5) controls P_LQ_K f_L, the **full physical output**. A finite compressed matrix measures Q_KP_LQ_K f_L (or an even narrower projection). Its output complement (I-Q_K)P_LQ_K f_L is not estimated by (5). Smoothness of the input does not make that output complement vanish: truncating the observation interval can create nonzero endpoint values and invalidate the periodic integration-by-parts argument for the output.

Finally, even with both adapters paid, A11's near-null complement bound controls only the complement of its response core. The actual core loading and its amplitude on this packet remain unbounded by any source-specific theorem in this round. A low rank or a fixed self-pairing is not that estimate.

Thus this result, together with the subsequent exact even-moment correction, pays the input side at paper level. It neither proves complete recovery of the physical output from the compressed matrix nor supplies the signed arithmetic upper. Step 4 remains OPEN.

## Evidence

- [Gevrey derivative derivation](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/CCM/UniversalSincInverseGevreyBounds.lean), freshly fetched and read this round.
- [Literal source definitions](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/OPICARound4/ActualSourceHyperbola.lean).
- [Actual prime-channel normalization](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/CCM/CanonicalSourceChannels.lean).
- A11 core-budget note; no native archive replay or new qualification is claimed here.

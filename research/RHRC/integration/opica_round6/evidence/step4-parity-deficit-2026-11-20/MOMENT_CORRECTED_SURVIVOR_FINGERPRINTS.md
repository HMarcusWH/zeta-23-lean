# Reconstructing the observed small-prime patterns on genuine survivors

**DERIVED on paper.** A single paid matching on the actual rough squarefree source can resolve the complete unsigned histogram of small-prime factors for every subpower cutoff. The estimate holds at the critical weighted square-error scale. It uses a correction computed from every removed target and its spent partner. It also gives a precise signed remainder for a prediction of the parity of the large cofactor. Its independent upper remains open.

## One selection for variable prime cutoffs

Freeze \(X\), its native \(y=\lceil\log_2 X\rceil^2\), and a complete terminal shell \([U,2U)\). Write \(D_z(n)=\prod_{y<p\le z,\ p\mid n}p\). The [small/large factor paper, equation (5)](../step4-one-sided-sieve-2026-11-19/SMALL_PART_LARGE_PART.md) gives, uniformly on every matching cell \(J\) of length \(H\ge U^{.48}\) and \(y<z\le U^{1/40}\),
\[
 \sum_{n\in J,\ P^-(n)>y}\log D_z(n)\ \ll HV(y)\log z,\qquad
 V(y)=\prod_{p\le y}(1-p^{-1}).
\]
Uniformity follows by summing its divisibility count with weights \(\log p\); the total floor error is \(U^{1/40+o(1)}\). No cancellation of Möbius signs enters.

Use \(a_j=2^{-j}\), \(z_j=U^{a_j}\), \(j\ge6\) with \(z_j>y\). Mark any row for which \(\log D_{z_j}(n)>C(j+1)^2 a_j\log U\) for some \(j\). Markov's bound and the convergent sum of \((j+1)^{-2}\) put at most \(O(HV(y)/C)\) additional rows in every matching cell. Fix \(C\) before selecting the cutoff to fit inside the positive donor margin in the [original three-stage matching](../step4-one-sided-sieve-2026-11-19/PRIME_FACTOR_PATHS.md). Add these rows to the targets and exclude them from the donors. The original occupancy estimates and exceptional-cell argument still pay the absolute one-sided energy change per shell. The [divisor-gap restriction](DIVISOR_GAPS_AND_SIGNED_HALVES.md) can be included in the same target list because it uses an additional \(o(HV)\) margin. Results proved for the separate aligned subpower cofactor selector have their own matching.

For each surviving \(n\), \(y<z\le U^{1/64}\) and \(a=\log z/\log U\), select \(j\) with \(a_{j+1}<a\le a_j\). Monotonicity gives
\[
 \log D_z(n)\le 2C(1+\log_2(1/a))^2 a\log U .
\]
When \(z\le y\) the product is 1. Thus the same survivor set has \(D_z(n)\le M=U^{o(1)}\) simultaneously for cutoffs with \(\sup_J\log z_J/\log U\to0\), including different choices at different nodes. The little-oh is uniform for any given envelope tending to zero. There is no simultaneous numerical rate over every possible sequence without such an envelope.

## Build a center from unsigned divisibility and the actual removal history

Fix a cell and its marked prime range \(y<p\le z\). Encode the complete marked fingerprint by the squarefree integer \(F=D_z(n)\). In the space of finite real measures on fingerprints let \(\mathbf e_b\) denote the point mass at \(b\). For each squarefree marked product \(d\) define
\[
 v_d=\sum_{b\mid d}\mu(d/b)\,\mathbf e_b,\qquad
 B_M(F)=\sum_{\substack{d\mid F\\d\le M}}v_d .
\]
Ordinary divisor inversion gives \(B_M(F)=\mathbf e_F\) exactly when \(F\le M\), where the assertion of equality is for every such \(F\). In fact if \(F>M\), the \(F\)-coordinate is absent so the vectors differ. The total mass of \(B_M(F)\) is always one for \(M\ge1\), since \(v_d\) has total mass zero for \(d>1\). Its coefficients for an over-limit removed row may be negative.

Let \(\mathcal R_J\) be **all** deleted source labels, targets and spent partners. For \(d\le M\) with every prime in the marked range, let \(N_J(d)\) be the raw unsigned count of native labels divisible by \(d\). For \(\sigma=1/2+\eta<1\), with \(\eta>0\) fixed, its genuine arithmetic marginal is
\[
 N_J(d)=\frac{H d_y}{\prod_{p\mid d}(p+1)}
       +O_\eta\!\big((U/d)^\sigma X^{o_\eta(1)}\big),
 \qquad d_y=\zeta(2)^{-1}\prod_{p\le y}\frac p{p+1}.
\]
Indeed write \(n=dm\), keep the squarefree rough \(m\) with \((d,m)=1\), and apply the scalar prefix convolution estimate at both endpoints of \(J/d\). Each additional exclusion \(p\mid d\) changes the cofactor density by \(p/(p+1)\), and changes the absolute correction bound by at most \(1+p^{-\sigma}\). Uniformly for \(d\le 2U\) the logarithm of the latter product is at most \(y^{-\sigma}\log(2U)/\log y=o(1)\). The exact floors at nonintegral endpoints are covered by the same bound. [Scalar and vector prefix estimates](SURVIVOR_HAAR_FINGERPRINTS.md)

Define the possibly signed center
\[
 C_J= H d_y\sum_{\substack{d\le M\\d\ {\rm squarefree,\ marked}}}
               \frac{v_d}{\prod_{p\mid d}(p+1)}
                 -\sum_{n\in\mathcal R_J} B_M(D_z(n)).
\]
Its total mass is exactly \(H d_y-|\mathcal R_J|\). Replacing its first coefficient by the measured raw \(N_J(d)\) instead of the displayed density would reconstruct the surviving histogram exactly. The estimate with the stated density therefore has actual mathematical content. If \(S_J\) is the unsigned vector of survivor counts, then
\[
 \begin{split}
 \|S_J-C_J\|_1
 &\le\sum_{d\le M} 2^{\omega(d)}
       \left|N_J(d)-H d_y/\prod_{p\mid d}(p+1)\right|\\
 &\ll_{\eta,\nu} U^{1/2+\eta}X^{o_\eta(1)}
                   M^{1/2-\eta+\nu} \qquad(\nu>0).
 \end{split}
\]
Here the first sum is over squarefree marked \(d\). For the second line extend the scalar upper to all integers and use \(2^{\omega(d)}\ll_\nu d^\nu\). With \(M=U^{o(1)}\), summing the squares over the original nodes and weights gives \(O_\epsilon(X^\epsilon)\) for every \(\epsilon>0\), because the total weight at each depth is \(2^{s_X}/U\). The bound holds also for arbitrary subsets of the nodes. The positive coordinatewise part \(C_J^+\) satisfies the same inequality against the positive \(S_J\). The signed center preserves the exact total above.

Passing raw Euler probabilities through a filter accepting only observed patterns can fail by a fixed power, even at \(z=(\log X)^3\). The corrected center uses fixed unsigned divisor densities and the complete known history of removed rows. Deleting just the point masses of over-limit rows would give the wrong center. [Sharp obstruction to the Euler comparison](SHARP_FINGERPRINT_THRESHOLD.md)

## A finite large-prime sector at each requested tolerance

There is another choice with a fixed-power cutoff. For prescribed \(\delta>0\) and integer \(k\ge1\), the [existing factor split, equation (1)](../step4-one-sided-sieve-2026-11-19/SMALL_PART_LARGE_PART.md) allows a fixed \(u>64\) and a paid matching with \(z=U^{1/u}\), \(D_z(n)\le U^\delta\), and \(k\le\omega(n/D_z(n))\le u+1\). One can combine these finite constraints with the previous matching by choosing the available target margins first. In this case the total weighted square error of the corrected histogram is \(O_{\delta,\epsilon'}(X^{\delta+\epsilon'})\) for every fixed \(\epsilon'>0\), by the displayed estimate with \(M=U^\delta\). For target accuracy \(X^\epsilon\), choose \(0<\delta<\min(1,\epsilon/2)\), then fix the matching and \(u\) before taking any horizon or selecting a packet. This is a tolerance-dependent fixed threshold; it gives no single fixed positive power with arbitrary accuracy.

## The part of the signed source this pays

For each cell let \(\phi_J(d)\) be any bounded prediction in \([-1,1]\) of the parity \(\mu(n/d)\) of the remaining large cofactor when \(d=D_z(n)\). The complete signed charge obeys the exact decomposition
\[
 r_J=\sum_d \mu(d)\phi_J(d)C_J(d)
 + \sum_{\rm survivors\ } \mu(D_z(n))\,[\,\mu(n/D_z(n))-\phi_J(D_z(n))\,]
 + E_J,\qquad
 |E_J|\le\|S_J-C_J\|_1 .
\]
The middle sum ranges over all survivors in \(J\). The proof adds and subtracts the predictor on the same genuine rows and uses squarefreeness. Thus \(\sum_J w_J|E_J|^2\ll_\epsilon X^\epsilon\) in the regimes above. This pays, independently, the complete error in inserting any such prediction into the small-prime histogram. It also bounds same-direction parity deviations after centering each coordinate at \(C_J(d)/2\), as in the [parity-deficit calculation](SURVIVOR_HAAR_FINGERPRINTS.md).

What is missing is a bound for the **sum of the first two terms** at common cofinal horizons. Choosing the measured conditional parity mean as a prediction simply moves the signed information into the first term. Taking \(\phi=0\) leaves the full arithmetic in the second. The remaining sign belongs to the same row and to a genuine large cofactor. Step 4 and RH remain **OPEN**.

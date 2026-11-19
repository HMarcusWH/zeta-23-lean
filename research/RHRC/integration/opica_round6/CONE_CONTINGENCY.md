# A large determinant on the genuine source

**DERIVED.** The small-cofactor estimate and the one-sided graph criterion can be evaluated on the same labels. Their \(2\times2\) sign table rules out a proposed shortcut. The raw positive covariance of these two arithmetic coordinates has almost linear weighted square energy even when the required full Möbius charge could be small.

Fix \(0<\kappa\) sufficiently small for the small-cofactor estimate and use whole dyadic base cells \(J\) of length \(H=U2^{-s_X}\) in a terminal shell \(U\asymp X\). For every nonzero squarefree rough label let \(b_n=-1\) if \(n/P^+(n)\le X^\kappa\) and \(b_n=1\) otherwise. Let \(a_n=\mu(n)b_n\). Both factors are computed on the literal input. Every prime and composite vertex contributes to the same table.

Write \(N\) for the number of labels, \(M\) for the number in the cone, \(f=\sum\mu(n)\), \(g=\sum_{\rm cone}\mu(n)\), \(a=\sum a_n\) and \(b=\sum b_n\). In the order \(++,+-,-+,--\) let the four counts be \(p,q,r,t\), with \(D=pt-qr\). When \(N>0\),
\[
       a=f-2g,\qquad b=N-2M,\qquad Nf-ab=4D,\qquad
       4D-2gb=2Mf .
\]
These identities include all same-sign and opposite-sign terms. Empty cells have zero charge and determinant. The third identity is also a finite Lean theorem. The fourth shows exactly what happens if the measured cone term is restored.

For whole base cells the elementary rough sieve gives \(N\asymp H/\log y\), \(y=\lceil\log_2X\rceil^2\). To remove squares in this lower bound, the total over \(p>y\) is \(O(H/y+\sqrt{2U})=o(H/\log y)\). The uniform prime counts for cofactors \(m\le X^\kappa\) and their harmonic mass give \(M\le C\kappa H/\log y\) with absolute \(C\) for all sufficiently small fixed \(\kappa\). Choose it before \(X\), so \(b/N\ge1/2\). The cone has signed charge
\[
       g=(1+o(1))H P_y/\log^2 U,\qquad
       P_y=\prod_{p\le y}(1-1/p)^{-1}.
\]
On the same cells the full rough Möbius sum is \(O_A(H/\log^A U)\), uniformly for every fixed \(A\). The base widths exceed the all-interval threshold with a strict power margin. Thus \(f=o(g)\) and
\[
        \frac{4D}{N}
          = f(1-b/N)+2g\,b/N \ \ge\ (1-o(1))g .
\]
The \(2^{s_X}\) base cells have weight \(1/U\) apiece. The sum of \(w_J[4D_J/N_J]_+^2\) on this shell is at least a constant times \(U2^{-s_X}P_y^2/\log^4 U=U^{1-o(1)}\). The elementary upper \(|4D/N|\le2N\le2H\) at each cell gives \(O(U2^{-s_X})\) on the shell. All inputs in this calculation are independent of a zeta zero or RH. [Signed cofactor drift](evidence/step4-prime-transport-2026-11-19/CONE_DRIFT.md) · [Large-cofactor comparison](evidence/step4-one-sided-sieve-2026-11-19/COMPLEMENT_POSITIVE_ENERGY.md) · [Rough counts and original partner pools](evidence/step4-prime-transport-2026-11-19/POSITIVE_DENSITY_RETIREMENT.md)

**Consequence for the next proof.** Dropping the product of the marginals from \(Nf=4D+ab\) would force a false subpower upper on a genuine arithmetic statistic. Subtracting the measured \(2gb\) recovers \(2Mf\) exactly and leaves the original sign question. The remaining estimate must control the difference with both terms present. The reproducible finite probe measures all four counts separately and checks both identities at every occupied node, including clipped terminal cells. Its deliberately larger cofactor cutoff is a sensitivity test. [Probe](cone_parity.py)
## Repeat the determinant calculation after matching

Every surviving label satisfies the strict inequality opposite to the defining small-cofactor cone. Consequently its cone coordinate is identically +1. In each survivor cell the negative column of the table is empty, the signed cone charge is zero, and the determinant vanishes identically. This is exact for either choice of real matching partners. The surviving signed charge is now the sum of the first coordinate and the product of the two signed margins divided by the survivor count equals that charge, for every nonempty cell.

This gives a source-specific test of what the matching preserves. Before selection the normalized determinant has almost linear positive square energy on a terminal shell. After selection it has zero energy. The paper matching estimate nevertheless bounds the change in the **true** one-sided square energy by a constant per whole shell. Thus applying the same cone determinant to the survivors discards precisely the statistic still to be estimated. The useful target is cancellation between the two surviving prime-factor parities in each cell with the original weights.

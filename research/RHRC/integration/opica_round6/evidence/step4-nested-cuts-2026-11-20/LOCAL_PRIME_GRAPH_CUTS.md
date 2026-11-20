# Optimizing the stopping cut and the prime-factor graph together

**DERIVED on paper.** This calculation combines the signed estimate on genuine prime-factor collisions with the disjoint unsigned counting bound. It applies to the raw terminal squarefree rough source and to complete native shells. It inherits the OPICA paper zero detector and the estimates stated in the [sparse-prime calculation](SPARSE_PRIME_FACTOR_CHARGES.md) and the [disjoint-cut calculation](DISJOINT_CUT_DISCREPANCY.md).

Choose a sign \(s\), a fixed \(0<\alpha<1/2\), and a fixed maximum degree schedule \(D(U)\ge 0\) with \(\log(1+D(U))=o(\log U)\). At each stopped cell \(J\) permit a different simple graph on primes \(p\ge U^\alpha\) with maximum degree at most \(D(U)\). The graph can be chosen using the actual observed factorization and signs of the entire cell. It is one graph for **all** rows in that cell. Remove a row if its prime factors contain an edge. Count a row once even if it contains several edges. Use the exact raw count of removed rows when centering the two surviving populations. This is an auxiliary projection of the raw arithmetic. Its error is paid on the signed source.

Write \(f_J\) for the raw charge, \(g_J\) for the genuine signed charge of all removed rows, and \(D_J\) for the raw unsigned discrepancy. The retained cost is exactly
\[
   \widetilde Q_J=\big[[s(f_J-g_J)]_+^2-D_J^2\big]_+ .
\]
Let \(S_*(a,c;X)\) be the sum over whole shells of the minimum of \(\sum_J\widetilde Q_J/U\), allowing both the cut and every cell's common graph to vary. Windows and cutoffs are as in the disjoint-cut paper. Finitely many cells and primes occur at each horizon. An empty graph is admissible and recovers the full-source cost on these coarse cells, so \(0\le S_*\le S_s\). There is no analogous permission to remove individual rows with no shared graph or no signed accounting.

Put \(B=\sup_\rho\Re\rho\), \(b=B-1/2\). The independent signed inclusion–exclusion estimate gives, for any fixed \(\eta>0\) and every chosen cell graph,
\[
    |g_J|\ll_{\eta,\alpha,D} U^{B-2\alpha b+\eta}.
\]
Uniformity follows from the common degree schedule and the spanning-tree count for overlapping prime edges. When applied to an individual interval one extends its graph to the shell by the same edge list, and takes its estimate on that interval only. No single graph has to describe different cells. The roughness and cofactor restrictions of the original arithmetic are held fixed.

If \(b>0\), select the actual early cell \(I\) furnished by the detector, with \(s f_I/\sqrt U\ge X^{b-o(1)}\), at depth strictly before the first eligible stopping level. Every allowed cut partitions \(I\) into at most \(U^c\) cells. Even with fully adaptive graph choices,
\[
    \frac1{\sqrt U}\sum_{J\subset I,\, J\in\mathcal C}|g_J|
        \ll U^{b-2\alpha b+c+\eta}.
\]
If \(c<2\alpha b\), fix \(\eta\) inside that gap. The exponent before the loss is nonnegative since \(2\alpha<1\), and \(U\le X\). The displayed cost has a strict power saving against the early signed excess. Therefore the retained rows in those cells still have total charge in polarity \(s\) at least \(\sqrt U X^{b-o(1)}\). Cauchy on the at most \(U^c\) descendants, followed by the disjoint squared discrepancy bound, gives
\[
   \liminf_{X\to\infty}\frac{\log(1+S_*)}{\log X}\ \ge\ 2b-c
           \quad (c<2\alpha b).
\]
An independent cofinal upper \(S_*\le C X^\lambda\) consequently implies
\[
   B\le\tfrac12+\max\{c/(2\alpha),(c+\lambda)/2\}.
\]
One may fix any single positive \(\alpha<1/2\) and use \(a=c/2\), \(c_i\downarrow0\), and \(\lambda_i\downarrow0\). Constants and the degree allowance must precede the cutoff choice for each test. An independently proved small signed cover after this permitted graph optimization would still force \(B=1/2\). The converse cofinal test under RH follows by using empty graphs and the earlier signed interval upper.

**What this buys.** A proposed bound may detect local prime-partner structure, choose which eligible graph to omit in each cell, and choose the stopping cut using the observed factorizations. To use this relaxation it must still control all other rows and use the corrected center. A row-specific graph would let one delete almost any factorizable row and defeats the uniform argument. The separate genuine matching construction allows other local exclusions by pairing both endpoints. Its survivors depend on that matching. Combining the two removals on an already selected source requires paying the cross-terms for the actual mixed selection. No such extra composition is presumed here.

**OPEN.** No admissible choice of cuts and shared prime graphs with the required signed upper at arbitrarily late native cutoffs has been exhibited. This is a relaxation of the original bound with its discarded arithmetic cost proved, rather than a zero exclusion or a new theorem of Lean.

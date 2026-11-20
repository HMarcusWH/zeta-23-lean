# External RH proof claims — exact Step 4 cross-check (20 November 2026)

**Disposition: RESEARCH AUDIT / CONDITIONAL REDUCTION. RH and Step 4 remain OPEN.**
This note makes no independent RH claim and changes no Lean theorem authority. Main is pinned at merge commit `3835cc66641fa48d78db932db1d32b57687f728c` (PR #303). Claim-source validity, formal source validation, and actual-source inequalities are distinct questions.

## 1. Alpöge/Claude: the terminal Lean step is short, but *not* the new arithmetic bound

Primary author's note: https://alpo.ge/remark.pdf

Unverified public source mirror:
- https://github.com/CocoSgt/riemann-hypothesis-lean/blob/main/src/Main.lean
- https://github.com/CocoSgt/riemann-hypothesis-lean/blob/main/src/Supplements/Kernels/MainTheorems.lean
- https://github.com/CocoSgt/riemann-hypothesis-lean/blob/main/src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean
- https://github.com/CocoSgt/riemann-hypothesis-lean/blob/main/src/Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean

The statement `UpperTheory.EveryCharacter` says that **all** Dirichlet L-functions have no zeros in Re(s)>1/2 (away from the trivial-character pole), i.e. a GRH-strength conclusion. The end of the imported chain is:

```lean
theorem allChi : UpperTheory.EveryCharacter :=
  UpperTheory.FinalTheorems.everyCharacter

theorem rhOfAll : RiemannHypothesis :=
  Formalism.VW.rh_of_every allChi
```

The decisive mathematical assertion is upstream of `allChi`, through `everyCharacter_of_row` and its automorphic prerequisites. A one-line theorem using `rhOfAll` is **not** an independent OPICA source estimate. A separate independent kernel/dependency audit is necessary before citing this as established RH. Verification status and constraints: https://github.com/SINF-KEN/rh-lean-check.

**Conditional opportunity:** if the external mathematics survives verification, search the dependency chain for an independently meaningful *quantitative signed-source inequality*, stated on the **same native Möbius population** used in PR #303. Neither "zero-free" nor "RH" itself is eligible as an independent Step 4 arithmetic premise.

## 2. Masullo: a direct countercheck to §1.4.3 (printed p.29)

Manuscript: https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

In §1.4.2 the approximate test is \(\phi_{h,\epsilon,z}(t)=h(t)(\rho_\epsilon*\phi_z)(t)\), where \(\phi_z(t)=t^{-z}\) for \(t>1\) and is zero below 1. The bump \(h\) has support in \((1,\infty)\), takes values in \([0,1]\), and is meant to increase pointwise to \(1_{(1,\infty)}\). In §1.4.3 the Archimedean integrals are asserted to be bounded by a common constant independent of the test \(\varphi\), for \(z\) in a fixed permitted compact \(K\).

**Countercheck (real place, rational field, trivial character, fixed \(z=2\)).** Let \(n>6\). Choose such a smooth compactly supported \(h_n\) with \(h_n(t)=1\) for all \(t\in[1+3/n,3/2]\); the family can be chosen monotone, with lower support endpoint tending to 1 and upper endpoint tending to infinity. Choose a nonnegative normalized approximate identity \(\rho_{\epsilon_n}\), with \(\epsilon_n\) sufficiently small for uniform approximation on that interval, so that
\[
(\rho_{\epsilon_n}*\phi_2)(t)\ge 1/4
\quad(1+3/n\le t\le3/2).
\]
This follows from uniform approximation of the continuous, strictly positive \(t^{-2}\) away from \(t=1\), and the choice of \(\epsilon_n\) may depend on \(n\).

The \(u=+1\) summand of the real-place contribution displayed in §1.4.3 is nonnegative and satisfies
\[
\begin{aligned}
I_n
&=\tfrac12\int_0^\infty \varphi_n(t)\,\frac{t^{1/2}}{|1-t|}\,\frac{dt}{t}\\
&\ge \tfrac18\int_{1+3/n}^{3/2}\frac{t^{-1/2}}{t-1}\,dt\\
&\ge \frac{1}{8\sqrt{3/2}}\log(n/6)\xrightarrow[n\to\infty]{}+\infty.
\end{aligned}
\]
The \(u=-1\) term vanishes for support on positive \(t>1\) in this trivial-character specialization. Therefore the claimed uniform absolute bound is **false as written for the stated approximating family**. In particular the stated bound cannot justify the Montel normal-family step without an additional cancellation, subtraction, modified space of tests, or other correction. This local countercheck **does not** establish that the entire proposed trace-formula strategy is impossible.

An independent textual completeness issue: Chapter 13, printed p.522, labels Theorem 13.3.1.2 with "Insert statement" and "State and prove the Main Theorems"; it is not a completed written proof in the circulating draft.

## 3. The shortest *honest conditional* Step 4 lemma on our native source

Reference (PR #303):
https://github.com/HMarcusWH/zeta-23-lean/blob/3ddb4dbc8ece682e6f49c3e63d89b71f6afd8748/research/RHRC/integration/opica_round6/evidence/step4-nested-cuts-2026-11-20/LOCAL_PRIME_GRAPH_CUTS.md

Use the paper's precisely defined \(S_{*,s}(a,c;X)\): sum of **complete, signed and discrepancy-corrected**, positive-part squared costs over disjoint admissible native stopping cuts and shared bounded-degree prime-removal graphs, for one fixed polarity \(s\), complete whole shells and original rough Möbius source. Every removed row and its unsigned correction are paid. Fix \(\alpha=1/4\) and an admissible common degree schedule once for each test.

**Single-parameter missing lemma:**
For every \(0<\eta<1/2\), there are \(C_\eta>0\) and arbitrarily large native \(X\) such that
\[
S_{*,s}(\eta/4,\eta/2;X)\le C_\eta X^{\eta/2}.
\tag{OPEN-SIGNED-UPPER}
\]
The constants, population, sign, degree schedule and depth parameters must be fixed *before* those late \(X\) are selected.

**Paper implication, conditional on its analytic detector estimates:**
Writing \(B=\sup_{\zeta(\rho)=0,\ 0<\Re\rho<1}\Re\rho\), the previously derived transfer gives
\[
B\le\tfrac12+\max\{c/(2\alpha),(c+\lambda)/2\}
=\tfrac12+\max\{\eta,\eta/2\}
=\tfrac12+\eta .
\]
Since this holds for every \(\eta>0\), \(B\le1/2\). The zeta functional equation and zero symmetry then imply RH. **This is a three-line conditional final argument, not a proof of OPEN-SIGNED-UPPER or the formalized growing-horizon transfer.**

### Two distinct unresolved proof obligations

1. **INDEPENDENT SOURCE BOUND:** Establish OPEN-SIGNED-UPPER from the true signed arithmetic of the actual rough squarefree source; do not infer it from an equivalent RH/GRH or a fictitious independent sign model. The already proved unsigned disjoint-cut bound does not supply the positive-versus-negative parity excess bound.
2. **FORMAL GROWING-HORIZON TRANSFER:** Kernel-check the analytic route with exact quantifiers, complete shell and selected-cell accounting, consistent constants, and the current source. The current Lean modules formalize distinct finite identities, not this asymptotic theorem.

A third-party GRH claim, even if ultimately validated, cannot be silently substituted for the independent Step 4 source bound. It could establish RH by an entirely different proof, but it does not retroactively prove the original OPICA route's independent arithmetic estimate.

**Next minimal experiment:** examine a certified intermediate statement in the Alpöge automorphic stack that bounds signed source terms uniformly at *growing, source-matched* cutoffs. Test it against PR #303's full raw charge, correction term, one-polarity stopping-cut cost and the signed removal ledger. If no such statement exists, continue directly with the source-specific cofinal upper rather than relabeling a zero-free theorem as that upper.

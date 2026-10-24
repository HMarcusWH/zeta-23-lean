# Independent mathematical review of the full H2a source and consumer

24 October 2026. Reviewed commit
`9a8b2a4baee49f2056c7945b1544a7bc2893735b`, tree
`6aa53d22d50d2aa24046d73b128c64a1d262f7f3`.

Verdict: no mathematical defect requiring a proof change was found in the
full determinant/actual-measure independence route or its physical expected
consumer. The proof retains the original grouped determinant, actual measures,
all available multiplicity jets and reflection quotient. The review is by a
non-author agent for H2a. It is mathematical supporting evidence, not external
human approval, a full-100 independent review seal, a fresh compiler receipt
or authority for any later source version. This reviewer authored separate
rate/physical-consumer/budget work; that work is not independently reviewed by
this verdict.

The reviewed files are `ConfluentProfiles.lean`, its full
`ExpectedConfluentProfiles.lean`, the relevant `CoPoissonJets.lean` definitions,
the original BUILD_SPEC, and compiler pins. Live bytes were checked against
the exact commit blobs. Their SHA-256 values are in
`H2A_MATH_REVIEW_CONTROLS_2026-10-24.json`, SHA-256
`ecaa7e9280eaeba5dba6988c6e186cb12b8ec32e4b4991067273931cfa9af4c8`.

## 1. Exact mathematical objects

The determinant concerns rows

\[
 p_n(\kappa)=\kappa(1/4-\kappa)^n,\qquad 0\le n<M,
\]

with columns `p_n^(k)(kappa_j)/k!`, `0≤k<m_j`, ordered in increasing blocks.
Its exact value is

\[
 (-1)^{M(M-1)/2}\prod_j\kappa_j^{m_j}
 \prod_{i<j}(\kappa_j-\kappa_i)^{m_i m_j}.
\]

The physical independence theorem concerns the embedded distributions of
the LITERAL `normalizedZeroMeasureJet rho k`, for every `k<zeroJetOrder rho`.
`zeroJetOrder` is `analyticOrderNatAt riemannZeta rho`; no simple-zero
assumption replaces the actual multiplicity. Nodes are distinct under
`rho ↦ spectralKappa rho = rho*(1-rho)`, not merely distinct as complex rho.
The expected consumer writes the normalized derivatives, both grouped
products and the entire actual measure family explicitly.

## 2. Actual measures to the first cell

`actual_jet_first_cell_pairing` uses the existing exact actual-measure
integral formula. A Schwartz test supported in `(1,2)` vanishes at EVERY
integer, so the punctured-lattice term disappears. This is a proved support
calculation, not an assumption that the measure equals its density globally.

A zero linear relation among the actual embedded measures therefore gives
zero density pairings for every compact smooth test in that cell. Local
integrability is proved from the actual density lemmas. Mathlib's open-set
fundamental lemma then gives almost-everywhere vanishing in `(1,2)`.
The original measure relation is exactly the hypothesis used in the
definition of linear independence; it is not an added conclusion-shaped
premise of the final independence theorem.

The passage to small logarithmic parameters is sound. For any epsilon>0,
the proof chooses an actual density-zero point in
`(1, exp(min(epsilon,log 2)))`, which has positive Lebesgue measure. Its
logarithm is a strictly positive, arbitrarily small parameter in the first
logarithmic cell. No unjustified transport of an a.e. set through log, no
global density continuity, and no differentiation at a lattice boundary is
used.

## 3. One-sided Taylor extraction

On the actual first cell the family is exactly

\[
 e^{u/2}g_\kappa(e^u)=\kappa\,Sh(1/4-\kappa,u),
 \qquad 0\le u<\log2.
\]

The entire kernel is expanded in odd powers of u. Its finite remainder is
bounded uniformly for the kappa variable in a unit neighborhood of the
chosen node. Cauchy's entire-function estimate bounds the k-th derivative;
division by k! exactly cancels its factorial. Thus the normalized parameter
jet has a remainder `O(|u|^(2n+3))`, with a constant independent of the
selected small u. A finite weighted sum retains that uniformity.

Strong induction extracts the odd coefficients from arbitrarily small
positive zeros. At step n the earlier coefficients have vanished, and the
bound becomes `|c_n u^(2n+1)|≤C u^(2n+3)`. Division by the strictly positive
power gives `|c_n|≤C u²→0`. Clearing the NONZERO odd factorial yields the
actual normalized polynomial rows. Neither a synthetic polynomial premise
nor an assumption that those rows already vanish appears in the primary.

The one-sided distinction is essential. From the displayed first-cell
formula the k=0 density has right leading term `kappa*u`, while the physical
family is zero on the cell to the left of x=1. For nonzero kappa, a global
smooth/Taylor argument across that lattice boundary would be invalid. The
implemented proof avoids that route correctly.

## 4. Determinant mechanism, sign and normalization

The algebra uses monic Newton polynomials. Their normalized Hasse evaluations
give an upper triangular Hermite matrix. The diagonal is the product of the
prior NONMATCHING node differences, with repeated matches supplying the
appropriate jet order. The monic polynomial basis change has determinant
one. This proves the full occurrence-ordered normalized Hermite product.

Multiplying the polynomial rows by X contributes one node factor per column;
the proof obtains this factor by adjoining a distinct zero node and expanding
the first column. Its nonzero-node premise is explicit. Replacing X^n by
`(1/4-X)^n` contributes `(-1)^(∑n)`, which is exactly
`(-1)^(M(M-1)/2)`. There is no missing normalization factor: Hasse evaluation
is separately identified with the ordinary k-th derivative DIVIDED by k!.

The grouped index is the explicit prefix map
`(j,k) ↦ sum_(i<j)m_i+k`. Its proved bijection supplies the inverse used by
the actual matrix. Within-block prior matches count exactly k. Each earlier
block supplies m_i differences to EACH of the m_j columns of the later block,
giving exponent `m_i*m_j`. The construction fixes column order, so an
unpriced arbitrary reindexing/permutation sign is not being suppressed.

## 5. Reflection, multiplicity and degenerate cases

Injectivity of spectral kappa removes reflected duplicates: rho and 1-rho
have the same node and may not be counted as two independent k=0 columns.
The primary handles this directly in its domain. Conjugate parameters are
not automatically identified; later realification must retain the actual
conjugation relation, as the separate finite-span construction does.

All orders `0,...,m_j-1` are retained for every actual analytic multiplicity.
No order at or beyond the multiplicity is inserted; beyond that range the
parent boundary term reappears. The actual nonzero-node proof uses the open
strip to exclude rho=0 and rho=1. The actual zero premise separately excludes
rho=1/2 where the local inverse would degenerate.

The algebra allows `M=0` and zero-size blocks. Empty matrices/products have
determinant one; zero-size blocks contribute no columns. Nonzero-node and
injectivity assumptions are still stated for all named blocks, including
dummy blocks. That is stronger than algebraically necessary for an inactive
block but agrees with the original contract and causes no physical loss for
actual strip zeros. The entire kernel also avoids an artificial square-root
singularity at kappa=1/4.

## 6. Independent adversarial computations

Fifteen exact-rational checks independently construct the polynomial rows,
evaluate normalized derivatives through binomial coefficients, and compute
the determinant by rational elimination. They cover the empty system,
all-zero multiplicities, one simple node, a third-order block, mixed
multiplicities, reversed order, kappa=1/4, an excluded zero node, an excluded
collision, a dummy block and four near-collision scales.

Examples: a single node kappa=2 with multiplicity three has normalized
determinant -8 but UNNORMALIZED derivative determinant -16. Nodes 2 and 5
with multiplicities two and three have normalized determinant 364500 and
unnormalized determinant 729000. Two simple nodes 2,5 give -30; reversing
their order gives +30. These checks specifically attack factorial and
orientation errors. Zero nodes/collisions give zero determinant. Distinct
auxiliary rational nodes `2,2+1/q` with multiplicities two and three have
determinants tending to zero, illustrating the absence of a uniform inverse
claim.

These are exact auxiliary algebra controls, not invented actual zeta zeros,
new Lean theorem authority or replacement compiler evidence. Their complete
matrices/results and the script hashable source are retained beside the
review.

## 7. Upstream and downstream implications

The accumulated-zero version of coefficient extraction is a useful reusable
lemma: a full analytic identity or a.e.-change-of-variable theorem is stronger
than the application needs. This compresses the physical independence route.
Likewise the occurrence-ordered Hermite theorem handles repeated nodes before
the grouped physical adapter adds its exact multiplicities and quotient.

The result provides the nontriviality/injectivity needed by the actual
finite-span sign restriction and Euclidean negative-mass budget. It gives
finite coefficient identifiability, not quantitative conditioning uniform
over changing zero systems. Neither the determinant nor independence rules
out the zeros or closes an RH-equivalent upper law.

## 8. Literature and novelty boundary

The determinant/Hermite mechanism is classical. Gautschi explicitly studies
derivative-column confluence and inverse bounds in his
[1962 paper](https://www.cs.purdue.edu/homes/wxg/selected_works/section_01/016.pdf);
his [1978 continuation](https://link.springer.com/article/10.1007/BF01432880)
gives lower inverse-norm bounds. This is prior machinery, including the
conditioning issue, rather than evidence for new zero-separation information.

Burnol's [2004 published paper](https://www.numdam.org/articles/10.5802/jtnb.434/)
and [author's text, Theorems 3.1–3.3](https://arxiv.org/pdf/math/0203120)
already treat zero-indexed systems with all derivative orders below actual
multiplicity. Consequently “zero jets and independence” is not a new general
idea. OPICA's narrower contribution is its explicit normalized order-zero
measure family and the proved physical first-cell bridge. No identity of
those carriers with Burnol's evaluators, or worldwide priority for the exact
OPICA specialization, is established by this review.

## 9. Disposition and next checks

No proof change is requested from this mathematical review. Continue the
owner's exact-source compiler/axiom/full-type/negative gates and canonical
namespace/import validation. Any later modified bytes need their own replay;
the present verdict is source-pinned to 9a8b. Investigate effective conditioning
of normalized, separated finite systems before using the determinant or
fixed-basis budget in a growing-horizon argument. RH and Step 4 remain OPEN.

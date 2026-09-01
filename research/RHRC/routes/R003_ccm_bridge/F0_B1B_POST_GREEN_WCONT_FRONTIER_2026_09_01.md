# F0-B1B post-green settlement — WCONT frontier

> **Claim firewall: RH remains OPEN.**
>
> This is the dated Post-Green Research Pass for PR #88. Live GitHub, exact Lean/compiler/CI and machine registries on the checked ref override this record if the repository later changes.

## Exact validated state

~~~text
PR #88 theorem head = 5e943d8cd6825c3c649198c52d90d1ed5d8d8b47
base = 1ad066f0a263725ea7b84447a637fcebda78e9ca
synthetic merge = 9eb9281394684600b35a58ce2cb3c757d06379cc
synthetic merge tree = d10e7b1e575624ab39fb445297f43168b1867ed1
RHRC #609 = SUCCESS
Permansson #382 = SUCCESS
PR state at settlement time = OPEN / NOT MERGED
merged main = 1ad066f0a263725ea7b84447a637fcebda78e9ca
merged through = PR #87
RH = OPEN
~~~

RHRC #609 passed the CCM build, ExceptionalZero build, no-placeholder gate, RHRC claim/regression suite, R003 normalization/source firewall, R004 scalar-shift audit and external-reference/oracle guards. Permansson #382 passed its independent Lean and placeholder/extra-axiom checks.

The production theorem axiom surface is:

~~~text
[propext, Classical.choice, Quot.sound]
~~~

No sorryAx survives.

## What became formally true

### PROVED — exact reserved modes

For N>=1, Lean defines legal Fin coordinates whose centered indices are exactly -1, 0 and +1.

The requirement N>=1 is real. N=0 has only one centered mode and cannot support the three-coordinate correction.

### PROVED — exact three-mode correction

For arbitrary u : Fin (2*N+1) -> C, write

~~~text
m0 = centeredMoment N 0 u
m1 = centeredMoment N 1 u
m2 = centeredMoment N 2 u.
~~~

The correction is supported only on centered modes -1,0,+1:

~~~text
c_-1 = (m1-m2)/2
c_0  = m2-m0
c_+1 = -(m1+m2)/2.
~~~

Lean proves

~~~text
M0(c)=-m0
M1(c)=-m1
M2(c)=-m2.
~~~

### PROVED — exact projection into the legal carrier

~~~text
boundaryFlatProject N hN u = u + c
~~~

satisfies BoundaryFlatCoefficients.

Production theorem:

~~~text
Zeta23.CCM.boundaryFlatProject_boundaryFlat
~~~

Lean also proves:

~~~text
Zeta23.CCM.boundaryFlatProject_eq_self_of_boundaryFlat
Zeta23.CCM.boundaryFlatProject_idempotent
~~~

So the operator fixes the boundary-flat sector and is idempotent.

### PROVED — exact endpoint/moment identities

At the left endpoint, the unwindowed finite trigonometric polynomial and its first two jets are exact scalar multiples of M0,M1,M2.

Production declarations:

~~~text
Zeta23.CCM.localizedFiniteFunction_zero_eq_centeredMoment_zero
Zeta23.CCM.localizedFiniteFirstJet_zero_eq_centeredMoment_one
Zeta23.CCM.localizedFiniteSecondJet_zero_eq_centeredMoment_two
~~~

These upgrade the earlier one-way “moments imply endpoint vanishing” logic into exact identities suitable for quantitative approximation work.

## What changed

Before #88, the primary F0-B1 route still had an algebraic legality seam:

~~~text
raw finite approximant
  -> ? exact legal boundary-flat approximant.
~~~

That seam is now closed on the exact green theorem head.

Combined with F0-B1A:

~~~text
arbitrary finite coefficients
  -> boundaryFlatProject
  -> exact boundary-flat coefficients
  -> global C² hard-window finite vector
  -> genuine W = canonicalSourceMatrix quadratic form.
~~~

Therefore finite legality is no longer the principal approximation obstruction.

The load-bearing internal frontier has moved to **WCONT-A**: prove exactly how much function-space control is sufficient to preserve the genuine Weil form and its strict negative margin.

## Upstream implications

### DERIVED — fixed finite-dimensional correction channel

The correction changes only three coefficient coordinates, independent of N.

This suggests the legality repair is rank at most three as a coefficient-space operation.

No LinearMap/rank theorem is currently formalized; keep this statement DERIVED.

### DERIVED — endpoint residuals are the right projection coordinates

Because #88 proves exact endpoint/moment formulas, approximation errors in value, first jet and second jet at the periodic endpoint translate directly into M0/M1/M2 residuals.

This is better than treating the moments as opaque coefficient sums.

### OPEN — quantitative correction bounds

The natural bounds

~~~text
|c_-1| <= (|m1|+|m2|)/2
|c_0|  <= |m0|+|m2|
|c_1|  <= (|m1|+|m2|)/2
sum |c_j| <= |m0|+|m1|+2|m2|
~~~

remain mathematically straightforward but are not yet theoremized in Lean.

Do not call them PROVED.

## Downstream implications

### WCONT-A can likely be smaller than previously expected

The genuine W summand is

~~~text
m_ρ * paperFT f(gamma_ρ)
    * conj(paperFT g(conj gamma_ρ)).
~~~

W2-A already proves the pair bridge under asymmetric regularity:

~~~text
f : C² + compact support
g : continuous + compact support.
~~~

ZeroSummability.lean already proves the inverse-square zero weight and the C² Fourier-decay mechanism.

This suggests only the first Fourier factor needs inverse-square decay; the second may use a plain support/L¹ bound.

### LEAD — candidate bilinear estimate

For a common compact support envelope of radius Λ, test a theorem of schematic form

~~~text
|W(f,g)|
  <= K_Λ * (||f||_1 + ||f''||_1) * ||g||_1.
~~~

This is OPEN.

If it is true and formally economical, diagonal continuity may follow from cross terms:

~~~text
e = p-h

W(p,p)-W(h,h)
  = W(e,p)+W(h,e).
~~~

The theorem must justify the required linearity/tsum rearrangements and supply an approximant-independent constant.

### Approximation target becomes narrower

After WCONT-A, the finite approximation theorem should be tailored to exactly its topology. The likely target is:

~~~text
h compact C²
tsupport h subset strict interior of (0,L)

-> exists raw finite Fourier q_N
   with q_N -> h
   in the WCONT-A topology
   and endpoint jets of q_N -> 0

-> p_N = boundaryFlatProject q_N
   remains close to h
   and is exactly boundary-flat.
~~~

No generic Fourier-density theorem is yet promoted.

## Resurrected routes

### F0-B2 direct localized-additive continuity

**Status: DORMANT / READY FALLBACK.**

#88 removes another reason to prefer F0-B2. The primary F0-B1 route now has both legal carrier and exact projector.

Reactivate F0-B2 only if genuine-W continuity becomes unexpectedly larger than direct localized-additive continuity.

### Boundary-killer multiplication

**Status: READY FALLBACK / LEAD.**

The five-mode pattern

~~~text
(1-cos(2πx/L))^2
~~~

automatically creates endpoint vanishing and preserves finite Fourier structure.

It remains a credible fallback if projection-smallness becomes awkward in the selected topology, but #88 makes exact projection the default.

### Witness regularity strengthening

**Status: DORMANT / READY SUPPORT.**

Do not strengthen the existing C² W1 witness unless WCONT-A or the actual approximation theorem forces higher regularity.

## New RH-relevant clues

### LEAD / HYPOTHESIS — constrained negative F1 vector is now realistic

If the primary route reaches F1, it should retain

~~~text
1^T u = 0
1^T D u = 0
1^T D²u = 0.
~~~

The canonical matrix already satisfies

~~~text
D M - M D = g 1^T - 1 g^T.
~~~

The three annihilated all-ones/Krylov channels may make the eventual negative finite vector more rigid than a generic negative vector.

No spectral or crossing theorem follows yet.

### LEAD — attack the admissible counterexample sector, not only RH

F1 would say that any off-line zero forces a negative canonical finite vector inside a codimension-three moment kernel. Post-F1, it may be more efficient to prove that this constrained negative sector is empty than to attack all negative vectors.

That is a possible obstruction-space formulation, not a current result.

## Falsification checks

1. **Merge status:** #88 is green but not merged at settlement time. Do not rewrite merged-main history.
2. **N=0:** the three-mode projector requires N>=1.
3. **Correction legality:** c=P(u)-u is generally not boundary-flat. Its hard-window zero extension is not automatically a global C² test.
4. **Quantitative gap:** #88 proves exact algebra but no correction norm bound.
5. **Continuity gap:** per-approximant Summable is not a family majorant.
6. **Cross-term algebra:** W linearity/conjugate-linearity and tsum rearrangements must be theoremized or justified where used.
7. **Support constants:** any WCONT bound must keep the support-envelope constant independent of the approximation index.
8. **Fourier bound:** the candidate L¹/C² estimate must handle the complex gamma strip exactly, including conjugated arguments.
9. **Approximation:** pinned Mathlib has no load-bearing ready Fejer theorem. “Standard approximation” is not a proof.
10. **Source firewall:** no internal F0-B theorem proves source QW_lambda or source negativity.
11. **Claim firewall:** F0-B1B is supporting infrastructure. RH remains OPEN.

## Highest-leverage next moves

1. Merge #88 when desired and verify permanent main SHA/tree.
2. Keep this Stage-B documentation/registry settlement aligned with the exact green theorem state.
3. Build WCONT-A as a quantitative bilinear theorem before any density library.
4. Derive diagonal/quadratic continuity from that theorem if the cross-term route is legal.
5. Build only the finite Fourier approximation required by WCONT-A.
6. Use endpoint jet/moment identities to prove projection correction smallness.
7. Transfer strict negativity to one boundary-flat finite vector.
8. Cash out immediately through F0-B1A to strengthened F1.
9. Stop at green F1 and perform a full Post-Green Research Pass before K0-K3.

## Standing questions

**Given everything now formally true, what becomes possible that was not possible before?**

Any raw finite coefficient vector with N>=1 can now be sent by an exact theorem-backed operator into the legal boundary-flat carrier on which genuine zeta W is already the canonical finite quadratic form.

**If this contains a clue toward RH, where does it propagate?**

It propagates directly into the F0-B approximation/sign-transfer seam and, if F1 is reached with the moment constraints intact, into the later displacement/Krylov rigidity stage.

**What experiment, lemma or reformulation most efficiently tests whether the clue is real?**

Prove or falsify the asymmetric WCONT-A bilinear estimate. If that estimate is small and clean, the remaining internal route may collapse to a narrowly tailored Fourier approximation theorem. If it becomes large or false, compare F0-B2 and the boundary-killer fallback before investing further.

RH remains OPEN.

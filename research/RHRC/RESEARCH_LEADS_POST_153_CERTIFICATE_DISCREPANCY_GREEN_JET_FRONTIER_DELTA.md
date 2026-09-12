# Post-#153 research delta — retained first-bad certificate, exact discrepancy, endpoint-jet frontier

Date: 2026-09-12

> **Claim firewall:** this document records the post-green research state after merged PR #153. Compiler/CI evidence is authoritative for theorem validity. DERIVED statements, external reviews and numerical experiments are not silently promoted to Lean theorems. **RH remains OPEN.**

## Exact authority

```text
live main after merged PR #153 = 474a88d76ecd2f4eee6178685b2e8d8b104171ca
live main tree = dd69f1c612047f2d2f15a7ba158664634284b42e

theorem-state anchor = PR #153 merge 474a88d76ecd2f4eee6178685b2e8d8b104171ca
validated theorem head = b6622dadab911008c0a7238e9dc711c6f9946302
validated theorem tree = dd69f1c612047f2d2f15a7ba158664634284b42e
RHRC #994 / run 34709905190 = SUCCESS
Permansson #767 / run 34709905198 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

The validated theorem head and merged `main` have the same theorem tree.

# What became formally true

## 1. The complete cell-minimal first-bad ancestry is now a first-class certificate

PR #153 adds

```text
RegularCellMinimalFirstBadCertificate
exists_regular_cellMinimal_firstBadCertificate
```

with fields retaining:

```text
Kstar
Nstar
L
p
1 <= Q
2 <= Kstar
1 <= Nstar
Nstar + 1 = Kstar
L in fixedCanonicalCutoffCell Q
ParityBad p L Kstar
forall M<Kstar, not CellAnyParityBad Q M
forall M<Kstar, not AnyParityBad L M
IntrinsicPredecessorRegular p L Nstar.
```

This closes the post-#150 information-loss concern for the selected first-bad construction. The whole-cell minimum is no longer only an internal proof device that disappears behind the outer existential tuple.

The historical theorem `exists_regular_cellMinimal_firstBad` remains a compatibility projection.

## 2. The regular negative-energy Schur state is also retained

PR #153 adds

```text
RegularCellMinimalNegativeEnergyCertificate
exists_regular_cellMinimal_negativeCanonicalEnergyCertificate
```

The retained state includes:

```text
firstBad certificate
predecessorNonnegative
x0
lam
lam < 0
exact cubicExplicitSchurScalar root equation
intrinsicPredecessorBlock ... x0 = intrinsicShellToPredecessor ...
parityCanonicalSourceEnergy(u0) < 0
canonicalSourceChannelEnergy(u0) < 0.
```

This matters mathematically: future arithmetic arguments can consume the exact forced-state hypotheses without reconstructing them from compressed theorem outputs or silently strengthening them.

## 3. A hypothetical off-line zero now reaches the retained certificate directly

PR #153 proves

```text
exists_regularFirstBad_negativeEnergyCertificate_of_offLine_zero
```

so the current contradiction route can be stated as

```text
off-line zero
  -> exists Q, Nonempty (RegularCellMinimalNegativeEnergyCertificate Q).
```

The older tuple wrappers remain available and unchanged as projections.

## 4. The exact source-atom energy is smooth

PR #153 defines

```text
sourceAtomRealEnergy K x omega
```

and proves

```text
sourceAtomRealEnergy_zero
contDiff_sourceEntry
contDiff_sourceAtomRealEnergy.
```

Thus the exact elementary source-atom real energy is `C^∞` in its source coordinate.

This is stronger regularity than the one-integration-by-parts FB-02 proof needs and is deliberately reusable by FB-03.

**Claim firewall:** smoothness is not endpoint flatness. No theorem in #153 proves the historical suggested order-seven/order-nine zero.

## 5. The pole channel has an exact cumulative-primitive derivative form

PR #153 proves the dictionary/source entry bridge and lifts it to matrix energy:

```text
dictionaryPoleRHS_basis_eq_sourceEntry_integral
canonicalPoleMatrix_apply_eq_sourceEntry_integral
matrixRealEnergy_canonicalPoleMatrix_eq_integral_sourceAtom
matrixRealEnergy_canonicalPoleMatrix_eq_deriv_integral.
```

The exact primitive is

```text
canonicalPoleCumulativeWeight t = 4 * sinh(t/2)
```

with derivative

```text
2 * cosh(t/2).
```

The right endpoint disappears in the first integration by parts because `sourceAtomRealEnergy ... 0 = 0`; the left endpoint disappears because the pole primitive is zero at zero.

## 6. The finite prime channel has the matching cumulative derivative form

PR #153 defines the finite von-Mangoldt staircase

```text
canonicalPrimeCumulativeWeight L t
  = sum q in Icc 2 floor(exp L),
      if log q <= t then Lambda(q)/sqrt(q) else 0
```

and proves

```text
matrixRealEnergy_canonicalPrimeMatrix_eq_cumulative_deriv_integral.
```

This is a finite exact theorem. The proof uses finite sums and ordinary interval integrals; no infinite distributional/Stieltjes interchange is imported into the theorem surface.

## 7. Pole-minus-prime cancellation is now an exact Lean theorem

PR #153 defines

```text
canonicalPolePrimeDiscrepancy L t
  = canonicalPoleCumulativeWeight t
    - canonicalPrimeCumulativeWeight L t
```

and

```text
canonicalPolePrimeDiscrepancyEnergy L K x
  = (1/L) * integral_0^L
      canonicalPolePrimeDiscrepancy L t
      * deriv(sourceAtomRealEnergy K x)(1-t/L) dt.
```

Headline theorem:

```text
matrixRealEnergy_pole_sub_prime_eq_discrepancy
```

Therefore

```text
E_pole(x)-E_prime(x)
  = discrepancyEnergy(x)
```

exactly under the production normalization.

This upgrades the strongest useful algebraic point from the post-#150 Astra review from **EXTERNAL DERIVED** to **PROVED**.

## 8. The full production channel is now written in discrepancy form

PR #153 proves

```text
canonicalSourceChannelEnergy_eq_discrepancy
```

so

```text
canonicalSourceChannelEnergy L K x
  = canonicalPolePrimeDiscrepancyEnergy L K x
    - matrixRealEnergy(reducedCanonicalArchDiagonalMatrix L K) x
    - matrixRealEnergy(reducedCanonicalArchOffDiagonalMatrix L K) x
    - canonicalArchScalarCorrection L * ||x||^2.
```

The active arithmetic problem can now work with the cancellation-preserving pole/prime object directly rather than estimating the two large channels independently.

# What changed

The post-#150 arithmetic programme had three immediate compression tasks:

```text
FB-01 retain the whole first-bad state
FB-02 theoremize pole-prime cancellation
FB-03 exploit boundary-flat endpoint structure
```

After #153:

```text
FB-01 = PROVED
FB-02 = PROVED
FB-03 = NEXT
```

Two formerly provisional pieces of the route are therefore no longer research hypotheses:

1. the full first-bad ancestry is available to downstream theorem statements;
2. the pole-prime discrepancy identity is exact repository theorem authority.

The remaining uncertainty is narrower and more informative:

```text
How much endpoint flatness does the exact production sourceAtomRealEnergy
actually inherit from the legal boundary-flat/parity constraints?
```

That answer determines how much smoothing is legally available.

# Correction to the old Riesz roadmap

The post-#150 synthesis derived, outside the Lean theorem surface, a candidate expansion

```text
g(omega) = -(8*pi^6/315)|M3|^2 omega^7 + O(omega^9)
```

and an even-parity candidate first term at order nine. From that it proposed sixth/eighth-order repeated integration by parts.

Those calculations remain valuable leads, but #153 does **not** prove them.

The project already has theorem-backed boundary-flat bridge statements for the localized finite function / centered moments at low order. That does not by itself prove the corresponding derivative order of

```text
g(omega)=sourceAtomRealEnergy K x omega.
```

The correct next theorem is therefore a discovery theorem, not a confirmation theorem:

```text
Given the exact legal x, what is the largest j for which g^(j)(0)=0?
```

If Lean proves order six generically and order eight in even parity, the old roadmap survives. If the order is lower or the parity upgrade fails, the roadmap must adapt immediately.

# Upstream implications

## 1. Certificate redundancy can now be examined safely

`RegularCellMinimalFirstBadCertificate` stores both

```text
cell_minimal
smaller_good.
```

Since `smaller_good` is a selected-aperture projection of whole-cell minimality plus `L_mem`, it may be logically redundant. It is still a useful cheap field for downstream proof engineering.

**LEAD:** prove the projection lemma explicitly and decide whether the structure should keep both fields for API convenience. Do not remove a field merely for aesthetic minimality if downstream arithmetic proofs benefit from the direct hypothesis.

## 2. The discrepancy interface should become the default paired-channel abstraction

The theorem-backed pole/prime cancellation means future arithmetic lemmas should normally consume

```text
canonicalPolePrimeDiscrepancy
canonicalPolePrimeDiscrepancyEnergy
```

rather than recreating separate pole/prime estimates.

A theorem that splits them again must explain why the cancellation loss does not swamp the selected residual.

## 3. A generic repeated-IBP abstraction is now more valuable than hard-coded order-six/eight lemmas

Define iterated primitives

```text
D^[0] = D
D^[r+1](t)=integral_0^t D^[r](s) ds.
```

Then left-endpoint vanishing is structural. A generic theorem with explicit right-endpoint derivative terms can be reused at whatever endpoint-jet order FB-03 proves.

This compresses the dependency graph and avoids duplicating nearly identical sixfold/eightfold proofs.

# Downstream implications

## 1. The selected state no longer needs hypothesis reconstruction

Arithmetic theorems can be stated directly against `RegularCellMinimalNegativeEnergyCertificate Q` or a deliberately smaller view extracted from it.

This reduces the chance of accidentally dropping whole-cell minimality, predecessor nonnegativity or the exact selected parity/aperture.

## 2. Pole-prime cancellation can be tested before any sign theorem

The #152 harness can be extended to compute the exact finite discrepancy pairing and, after FB-03, the exact theorem-backed smoothed representation.

This creates a strong prove/falsify loop:

```text
Lean identity -> numerical/interval stress test -> refined scoped inequality -> Lean proof attempt.
```

## 3. The decisive theorem remains much smaller than universal positivity

The required contradiction still only needs

```text
Ecanonical(c-x0) >= 0
```

on the exact forced retained state.

Universal positivity of every legal state is stronger than necessary and remains a broad fallback.

# Resurrected routes

## Cross-parity / finite-tower regularity

Because the selected first-bad ancestry is now retained explicitly, simultaneous both-parity or finite-tower regularity can be stated without rebuilding the cell minimum. This remains optional support work.

## Low-rank displacement with a true preimage

The selected predecessor is regular and the exact preimage exists. Low-rank displacement may therefore be revisited as a possible compression of `<b,A^-1b>` into a few source moments.

Generic displacement alone remains insufficient by countermodel; any revival must spend exact canonical coefficients.

## Positive-pivot / first-sign-flip recurrence

Whole-cell/smaller-size ancestry is now a first-class field. If a canonical recurrence for Schur pivots can be identified, the “all previous good, selected successor bad” pattern may become usable. No such recurrence is currently proved.

# New RH-relevant clues

## LEAD — left-anchored smoothing is structurally natural

Let

```text
h(t)=g(1-t/L).
```

The right endpoint `t=L` corresponds to the source coordinate `omega=0`, while every iterated discrepancy primitive anchored at zero vanishes at the left endpoint. This makes repeated integration by parts a natural way to spend endpoint jets without differentiating the prime staircase.

The key issue is the **actual** right-endpoint jet order.

## LEAD — the transformed target may only need a test-class inequality

The selected residual is not an arbitrary function. It belongs to a tightly constrained finite boundary-flat/parity/first-bad test class.

Even if an iterated discrepancy primitive changes sign globally, the pairing against the restricted derivative family may still have a fixed sign or admit a sharp archimedean budget.

Therefore global positivity of the smoothed discrepancy is not the only possible closure theorem.

## LEAD — attack the counterexample space rather than RH directly

A hypothetical off-line zero must now produce a state satisfying simultaneously:

```text
whole-cell first-bad ancestry
selected predecessor nonnegativity
selected regularity
exact A x0=b
negative explicit root
negative exact source-channel energy
exact discrepancy normal form.
```

Each additional theorem about endpoint jets or transformed pairings shrinks this admissible counterexample space. That is legitimate progress even before a full sign theorem is available.

# Falsification checks

## 1. Jet-order falsification

Fastest test: symbolically/numerically compute low-order derivatives of `sourceAtomRealEnergy` on exact rational boundary-flat/parity vectors and search for the first nonzero derivative.

This is discovery evidence only, but it can prevent wasted Lean work on a false order claim.

## 2. Degenerate dimensions

Test the smallest legal `N` and both parity sectors. Low-dimensional degeneracies may force extra moment vanishings not present generically. A theorem inferred from only those cases would be over-scoped.

## 3. Scaling

`sourceAtomRealEnergy` is quadratic in the test vector. Endpoint-jet statements should be homogeneous and must not rely on a hidden normalization unless explicitly stated.

## 4. Parity upgrade

Do not infer “even parity -> odd moments vanish -> order-nine energy zero” without tracing the exact centered-index/moment convention through the energy formula.

## 5. Boundary terms and powers of L

Every repeated integration by parts must track the exact chain-rule factors `(-1/L)^j` and every right-endpoint term. A sign or power mistake here would corrupt the arithmetic target while leaving the high-level idea plausible.

## 6. Archimedean remainder

Even a favorable discrepancy pairing is not enough if the reduced archimedean diagonal/off-diagonal/scalar budget can dominate with the wrong sign. FB-04 should test the full exact channel expression, not only `D_L` in isolation.

## 7. Modified-source robustness

If a proposed sign proof works unchanged under broad perturbations of the von-Mangoldt weights, that is a warning: earlier countermodels show exact arithmetic coefficients matter. Robustness is acceptable only if the proof explains why the perturbation class preserves the needed property.

# Highest-leverage next moves

1. **Prove the exact selected-vector boundary-flat interface needed by the source-atom calculation.** Avoid an accidental mismatch between coefficient/function/moment conventions.
2. **Determine the actual endpoint jets of `sourceAtomRealEnergy` at zero.** This is the highest-information theorem currently available.
3. **Build one generic iterated-primitive / repeated-IBP theorem with explicit boundary terms.** Do not hard-code six/eight integrations.
4. **Instantiate it exactly to the proved jet order.** Export the transformed discrepancy identity without claiming a sign.
5. **Extend the #152 harness to that exact transformed object and full arch/scalar budget.** Try to falsify the candidate sign before long proof investment.
6. **Only then attempt the scoped theorem `Ecanonical(c-x0)>=0`.**

# Standing questions

Given everything now formally true, what becomes possible that was not possible before?

- downstream arithmetic theorems can consume the full forced-state ancestry directly;
- pole/prime cancellation can be preserved exactly inside Lean before estimation;
- repeated smoothing can be stated generically and instantiated to a discovered jet order.

If this contains a clue toward RH, where does the clue propagate?

```text
boundary-flat/parity geometry
  -> endpoint jets of exact source-atom energy
  -> legal amount of discrepancy smoothing
  -> transformed selected-residual arithmetic inequality
  -> same-state nonnegative sign
  -> contradiction with retained negative certificate.
```

What experiment or lemma most efficiently tells us whether the clue is real?

**The exact endpoint-jet theorem for `sourceAtomRealEnergy` at zero.** It either validates the high-order smoothing route, weakens it to the true order, or falsifies the route before more arithmetic infrastructure is built.

**RH remains OPEN.**

# RHRC — Riemann Hypothesis route-closure control plane

> **Claim firewall: RH remains OPEN.**

## Current authority snapshot

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

Live GitHub head + exact Lean compiler + CI are authority. Control v2 may select research actions but may not promote theorem or terminal RH status.

## Theorem-backed route

```text
finite off-line-zero obstruction / legal approximation                 PROVED
canonical finite negative obstruction                                  PROVED / #94
centered N-flow / parity / first-bad / shell / Schur package            PROVED / #100-#128
source-explicit cross-parity transfer                                   PROVED / #129
exact canonical source-moment decomposition                             PROVED / #131
denominator-free zero-shift source transport                            PROVED / #134
absolute canonical source-energy decomposition                          PROVED / #136
exact canonical source pairing + one-step determinant                   PROVED / #137
aperture freedom at every sufficiently large L                          PROVED / #140
fixed-cell actual-source continuity + fixed-witness persistence          PROVED / #142
frozen/log-cover source/predecessor scaffold                            PROVED / #144
scalar removable analytic/production bridge                             PROVED / #145-#146
fixed-unit archimedean parameter holomorphy                             PROVED / #148
assembled full frozen source/predecessor holomorphy                     PROVED / #150
deck-forced determinant nonidentity                                     PROVED / #150
open-interval actual predecessor regular selection                      PROVED / #150
cell-minimal regular first-bad selection                                PROVED / #150
regular zero-shift exact canonical source-channel energy < 0            PROVED / #150
retained full first-bad / negative-energy certificates                  PROVED / #153
off-line zero -> retained finite regular negative certificate           PROVED / #153
exact finite pole-prime discrepancy identity                            PROVED / #153
full source-channel discrepancy normal form                             PROVED / #153

actual source-energy endpoint jet order                                 OPEN / NOW
theorem-backed repeated-IBP / Riesz normal form                         OPEN
regular selected-residual arithmetic sign                               OPEN
negative-root exclusion                                                  OPEN
outside-strip/trivial-zero seam + terminal RH bridge                     OPEN
RH                                                                       OPEN
```

## What #153 changed

The information-loss issue identified after #150 is closed for the selected state: the full whole-cell first-bad ancestry and the exact negative-energy Schur state now persist in first-class certificate structures rather than being compressed into tuple-only interfaces.

The arithmetic cancellation issue also moved. Pole and prime are no longer merely two large channels to be compared externally. The theorem

```text
matrixRealEnergy_pole_sub_prime_eq_discrepancy
```

proves an exact finite cumulative-discrepancy representation, and

```text
canonicalSourceChannelEnergy_eq_discrepancy
```

places it inside the production source-channel energy.

The current problem is therefore not “can we retain the forced state?” or “can we reproduce the pole-prime cancellation?” Those are theorem-backed.

The immediate question is:

```text
What endpoint jets of sourceAtomRealEnergy are ACTUALLY forced
by the exact boundary-flat/parity hypotheses?
```

Only after that answer is proved should repeated integration by parts be instantiated.

## Current execution priority

1. **Endpoint-jet discovery.** Prove the exact derivative vanishing order of `sourceAtomRealEnergy` at zero under theorem-backed boundary-flat constraints; test parity enhancement without assuming it.
2. **Generic smoothing theorem.** Build iterated primitives and repeated integration by parts with all boundary terms explicit.
3. **Instantiate only to the proved order.** Produce the exact transformed discrepancy identity licensed by step 1.
4. **Use the #152 harness to falsify candidate sign mechanisms.** Extend it to the theorem-backed transformed quantity and preserve the remaining arch/scalar budget.
5. **Prove the independent scoped sign** `Ecanonical(c-x0)>=0` on the exact retained forced state.
6. **Compose same-state signs to exclude the hypothetical off-line zero.**
7. **Close the explicit outside-strip/trivial-zero seam and terminal Mathlib wrapper.**

Universal A4b2b domination remains a broad fallback if a genuinely independent canonical arithmetic mechanism appears.

## Formal endpoint and derived interpretation

At the selected retained state:

```text
whole-cell K* minimality      theorem-backed
smaller sizes good at L       theorem-backed
A>=0                          theorem-backed
A regular                     theorem-backed
A>0                           DERIVED finite Hermitian consequence
unique x0 with A x0=b         theorem-backed
lam<0 + explicit root         theorem-backed
Ecanonical(c-x0)<0            theorem-backed
```

Separately, the exact source channel has the theorem-backed discrepancy form

```text
Ecanonical(x)
 = discrepancyEnergy(x)
   - reducedArchDiagonalEnergy(x)
   - reducedArchOffDiagonalEnergy(x)
   - scalarCorrection*||x||^2.
```

The historical post-#150 order-seven/order-nine source-energy expansion remains **DERIVED / LEAD**, not theorem authority.

## Falsification memory

Do not silently re-enter these shortcuts:

- global aperture Loewner monotonicity — experimental mixed-sign derivative evidence;
- global zero-shift Schur monotonicity — experimental sign changes;
- universal positive elementary source atom — experimental sign changes;
- independent loose channel majorants — conditioning/cancellation warning;
- direct coth/deck common-lattice identification — coordinate mismatch without a new transform theorem;
- pre-assumed order-seven/order-nine source-energy endpoint flatness — must be proved from production definitions.

After #153 there is an additional design rule: if a proof splits pole and prime back apart, it is discarding an exact cancellation-preserving theorem and must justify the loss quantitatively.

## Current research records

- `CURRENT_RESEARCH_PLAN.md` — execution order and theorem gates.
- `RESEARCH_LEADS_POST_153_CERTIFICATE_DISCREPANCY_GREEN_JET_FRONTIER_DELTA.md` — newest post-green synthesis.
- `RESEARCH_LEADS_POST_150_REGULARIZATION_CLOSED_ARITHMETIC_FRONTIER_DELTA.md` — historical pre-#153 arithmetic synthesis.
- `external_reviews/ASTRA_POST_150_ARITHMETIC_FRONTIER_ASSESSMENT_2026_09_12.md` — historical external provenance.
- `countermodels/POST_150_ARITHMETIC_DIAGNOSTICS_2026_09_12.md` — discovery/falsification memory.
- `countermodels/POST_150_SELECTED_RESIDUAL_SCOPE_AUDIT_2026_09_12.md` — #152 finite certification harness audit.
- `OBSTRUCTION_LEDGER.md` — accumulated historical blockers; current additive state is in the newest delta.
- `DEAD_ROUTES.md` — quarantined routes.
- `routes/R003_ccm_bridge/README.md` — active route theorem surface.
- `control_v2/README.md` — executable research routing.

Older dated deltas and route settlements remain historical evidence and are not rewritten to look current.

## Permanent firewalls

- RH remains OPEN.
- theorem authority is through #153; machine claim promotion remains separate.
- negative exact selected energy is not a contradiction without an independent nonnegative sign theorem.
- exact discrepancy identity is not a discrepancy sign theorem.
- smoothness is not high-order endpoint vanishing.
- boundary-flat moment constraints do not automatically license the historical sixth/eighth-order Riesz formulas.
- external derivations and numerical experiments are not Lean authority.
- interval-certified finite numerical failures are scoped falsification evidence only.
- no factorwise division by `alpha`, `Gamma`, overlap or source moment without theoremized nonzeroness.
- `D` remains algebraic, not unitary/isometric.
- terminal negative-root exclusion still needs the outside-strip/trivial-zero seam before the Mathlib `RiemannHypothesis` wrapper.

**RH remains OPEN.**

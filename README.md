# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **RH remains OPEN.**

This fork preserves the upstream Zeta23 theorem package while adding an opt-in RH-directed research programme under `Zeta23/CCM`, `Zeta23/ExceptionalZero` and `research/RHRC`.

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

Live GitHub head + exact Lean/compiler/CI remain authoritative.

## Current theorem ladder

```text
off-line zeta zero
  -> legal finite canonical negative obstruction                     PROVED
  -> global first bad + predecessor parity nonnegativity             PROVED
  -> shell/KKT/Schur/secular machinery                               PROVED
  -> source-explicit transfer                                       PROVED / #129
  -> exact canonical source-moment decomposition                    PROVED / #131
  -> denominator-free zero-shift kernel/source transport            PROVED / #134
  -> scalar-sensitive absolute canonical source energy              PROVED / #136
  -> exact source pairing + one-step determinant                    PROVED / #137
  -> every sufficiently large aperture has finite badness           PROVED / #140
  -> fixed-cell same-witness strict negative persistence            PROVED / #142
  -> frozen production source/predecessor + log-cover scaffold      PROVED / #144
  -> removable scalar analytic/production bridge                    PROVED / #145-#146
  -> fixed-unit archimedean parameter holomorphy                    PROVED / #148
  -> full frozen source/predecessor coordinate holomorphy           PROVED / #150
  -> deck-forced determinant nonidentity                            PROVED / #150
  -> regular predecessor in every nonempty open cell interval       PROVED / #150
  -> regular cell-minimal first-bad negative energy                 PROVED / #150
  -> interval-certified selected-residual falsification harness     TOOLING / #152
  -> retained whole-cell first-bad certificate                      PROVED / #153
  -> retained full regular negative-energy Schur certificate        PROVED / #153
  -> off-line zero => retained negative-energy certificate          PROVED / #153
  -> exact finite pole-prime discrepancy identity                   PROVED / #153
  -> full source-channel discrepancy normal form                    PROVED / #153

  -> exact source-energy endpoint jet order                         OPEN / NEXT
  -> theorem-backed repeated-IBP / Riesz representation             OPEN
  -> scoped selected-residual nonnegativity                         OPEN
  -> negative-root exclusion                                        OPEN
  -> outside-strip/trivial-zero seam + Mathlib RH wrapper            OPEN
  -> RH                                                               OPEN
```

## What #153 changed

PR #153 closes the first two arithmetic-frontier work packages identified after #150.

### FB-01 — retained first-bad state

The project now has first-class certificate structures instead of only compressed existential tuples:

```text
RegularCellMinimalFirstBadCertificate
RegularCellMinimalNegativeEnergyCertificate
```

The retained state includes whole-cell minimality, selected-aperture smaller-size goodness, regularity, predecessor nonnegativity, the negative explicit Schur root, the exact preimage equation `A x0=b`, and strict negative canonical energy. The compatibility tuple theorems remain available as projections.

The ExceptionalZero wrapper now exports:

```text
exists_regularFirstBad_negativeEnergyCertificate_of_offLine_zero
```

so a hypothetical off-line zero reaches the richer certificate directly.

### FB-02 — exact finite pole-prime cancellation

PR #153 theoremizes the exact production identity

```text
matrixRealEnergy(canonicalPoleMatrix) - matrixRealEnergy(canonicalPrimeMatrix)
  = canonicalPolePrimeDiscrepancyEnergy
```

with

```text
canonicalPolePrimeDiscrepancy L t
  = 4*sinh(t/2)
    - sum_{2 <= q <= floor(exp L), log q <= t} Lambda(q)/sqrt(q).
```

The full source-channel theorem is

```text
canonicalSourceChannelEnergy_eq_discrepancy
```

which preserves pole/prime cancellation before subtracting the reduced archimedean diagonal, reduced archimedean off-diagonal, and scalar-correction channels.

This is a finite exact identity. It does not use an infinite Stieltjes interchange and it is not a sign theorem.

## Active path

```text
PROVED THROUGH #153
  off-line zero
    -> retained regular cell-minimal first-bad certificate
    -> exact predecessor nonnegativity / regularity / A x0=b
    -> exact canonical source-channel energy < 0
    -> exact finite pole-prime discrepancy normal form

NOW — FB-03
  determine the actual endpoint jets of sourceAtomRealEnergy at omega=0
  from theorem-backed boundary-flat/parity information
    -> build a generic iterated-primitive / repeated-integration-by-parts lemma
    -> instantiate only to the formally proved jet order
    -> expose the exact transformed arithmetic target

THEN
  feed that theorem-backed representation into the #152 falsification harness
    -> kill overbroad sign mechanisms early
    -> prove the scoped selected-residual sign Ecanonical(c-x0) >= 0

TARGET
  same-state contradiction with the #153 retained negative certificate
    -> negative-root exclusion
    -> explicit outside-strip/trivial-zero seam
    -> Mathlib RiemannHypothesis wrapper
```

Universal one-step domination remains a broad fallback if a genuinely independent canonical arithmetic mechanism is discovered. Repackaging successor positivity under another name does not count as a reduction.

## Important status distinctions

At the selected forced state:

```text
whole-cell K* minimality      theorem-backed / #153 certificate
smaller sizes good at L       theorem-backed / #153 certificate
A >= 0                        theorem-backed
A regular                     theorem-backed
A > 0                         DERIVED finite Hermitian consequence
A x0 = b                      theorem-backed
lam < 0 and explicit root     theorem-backed
Ecanonical(c-x0) < 0          theorem-backed
```

The exact pole-prime discrepancy identity is now **PROVED**, not external-derived.

The historical post-#150 calculation suggesting an order-seven generic source-energy zero, order-nine even-parity zero, and sixth/eighth-order Riesz smoothing remains **DERIVED / LEAD** until Lean proves the actual endpoint jets. Existing boundary-flat function/moment bridge theorems do not by themselves establish those source-energy derivative orders.

## Current falsification memory

Do not silently re-enter these default shortcuts:

- global aperture Loewner monotonicity;
- global zero-shift Schur monotonicity;
- universal positive elementary source-atom energy;
- loose independent pole/prime/arch/scalar majorants that destroy the exact cancellation now theoremized in #153;
- direct identification of the aperture `coth` singularity lattice with the logarithmic-cover deck lattice.

The #152 interval harness is a falsification/certification instrument, not theorem authority. A floating candidate is only an experimental signal; an Arb enclosure can rigorously falsify the finite scoped mechanism it checks, but does not become a Lean theorem or certify the stronger whole-cell ancestry automatically.

## Documentation authority

Current living state is maintained in:

- `research/RHRC/CURRENT_RESEARCH_PLAN.md`;
- `research/RHRC/RESEARCH_LEADS_POST_153_CERTIFICATE_DISCREPANCY_GREEN_JET_FRONTIER_DELTA.md`;
- `research/RHRC/DOCUMENTATION_AUTHORITY.md`;
- `research/RHRC/VALIDATION_PROTOCOL.md`;
- `research/RHRC/routes/R003_ccm_bridge/README.md`;
- `research/RHRC/control_v2/README.md`.

Older dated deltas, external reviews, countermodel reports and release audits remain historical evidence and are not rewritten to look current. The accumulated `RESEARCH_LEADS.md` and `OBSTRUCTION_LEDGER.md` are historical inventories; current anchors and additive post-#153 state are carried by the living SSOTs and newest dated delta.

## Permanent firewalls

- RH remains OPEN.
- compiler/CI validity attaches to the exact checked object.
- theorem authority through #153 is not automatic machine claim promotion.
- a retained negative certificate is a countercertificate, not a contradiction.
- the pole-prime discrepancy identity is an identity, not a positivity theorem.
- boundary-flat moment information is not automatically a seventh/ninth-order source-energy jet theorem.
- Riesz smoothing is not an arithmetic sign theorem.
- interval-certified finite numerics are not Lean theorem authority.
- generic/modified-source countermodels are not zeta counterexamples.
- no factorwise division by unproved transfer/source quantities.
- `D` remains algebraic, not unitary/isometric.
- negative-root exclusion is not the terminal Mathlib `RiemannHypothesis` statement without the final seam.

**RH remains OPEN.**

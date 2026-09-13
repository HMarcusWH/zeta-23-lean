# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **RH remains OPEN.**

This fork preserves the upstream Zeta23 theorem package while adding an opt-in RH-directed research programme under `Zeta23/CCM`, `Zeta23/ExceptionalZero` and `research/RHRC`.

## Current authority snapshot

```text
live main after merged PR #157 = e304f07c9e83165ebf066db0d67c2cc24f8961c2
live main tree = 706dfde7f9e7b0b8403a671769d424ac7862f5e7

latest theorem-bearing PR = #157
validated theorem head = 4b517db1d4a50277d325e77e771a30fc0db5c777
validated theorem tree = 706dfde7f9e7b0b8403a671769d424ac7862f5e7
RHRC #1017 / run 34731682546 = SUCCESS
Permansson #790 / run 34731682544 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

Live GitHub head + exact Lean/compiler/CI remain authoritative. The validated #157 head and merged `main` are different commits but share the same theorem tree.

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
  -> aperture freedom / regular selected first bad                  PROVED / #140-#150
  -> interval-certified selected-residual falsification harness     TOOLING / #152
  -> retained whole-cell first-bad certificate                      PROVED / #153
  -> exact finite pole-prime discrepancy identity                   PROVED / #153
  -> finite discrepancy integrability                              PROVED / #155
  -> anchored Riesz primitives + legal conditional smoothing        PROVED / #155
  -> source-coordinate oddness + all even endpoint jets             PROVED / #155
  -> genuine complex production D transport                         PROVED / #157
  -> boundary-flat jets 1..6 / even jets 1..8                       PROVED / #157
  -> exact complete Riesz-6 / even Riesz-8 source channel           PROVED / #157
  -> retained complete Riesz-6 negativity                           PROVED / #157
  -> retained complete Riesz-8 negativity when first-bad parity even PROVED / #157
  -> off-line zero -> retained complete Riesz-6 negative certificate PROVED / #157

  -> specific FB-04 arithmetic-mechanism falsification              OPEN / NEXT
  -> independent nonnegative sign for complete transformed residual OPEN
  -> same-state contradiction / negative-root exclusion             OPEN
  -> outside-strip/trivial-zero seam + Mathlib RH wrapper           OPEN
  -> RH                                                              OPEN
```

## What #157 actually proved

PR #157 closes the former FB-03E/FB-03F theorem frontier.

### Complex production D transport

**PROVED:** the source-coordinate second-derivative transport is established on the genuine complex production `sourceAtomRealEnergy`. The proof explicitly handles complex coefficients, exposes the rank-two defect before zero-sum cancellation, and does not silently promote a real-vector helper.

### Production endpoint jets

**PROVED:** every boundary-flat production carrier has source-energy jets 1 through 6 equal to zero. Every even boundary-flat production carrier has jets 1 through 8 equal to zero.

### Exact complete production Riesz representations

**PROVED:** boundary-flat carriers satisfy exact order-6 Riesz equality; even boundary-flat carriers satisfy exact order-8 Riesz equality. The complete transformed channel is `canonicalRieszSourceChannelEnergy`, retaining the transformed pole-prime discrepancy, both reduced archimedean channels and the scalar correction.

### Retained transformed-negative state

**PROVED:** every retained `RegularCellMinimalNegativeEnergyCertificate` carries strict complete Riesz-6 negativity; when its retained first-bad parity is even, it also carries strict complete Riesz-8 negativity.

**PROVED:** a hypothetical off-line zero propagates to a retained regular first-bad certificate with complete order-6 Riesz source-channel energy `< 0`.

This is not a contradiction. It is the transformed negative side of the desired same-state contradiction.

## What #157 did not prove

No current Lean theorem establishes:

```text
an independent nonnegative sign for the complete transformed residual
an exact Riesz boundary-term sign theorem
exact seventh/ninth leading-jet coefficient formulas
negative-root exclusion
outside-strip/trivial-zero terminal seam
RiemannHypothesis
```

The post-green calculation

```text
g^(7)(0) = -2*(2*pi)^6*|M3|^2
g^(9)(0) =  2*(2*pi)^8*|M4|^2
```

remains **DERIVED / OPEN IN LEAN**. #157 theoremizes the zero cases needed for Riesz 6/8, not those exact leading coefficients.

## Falsified shortcut

Exact `K=2` boundary-flat fixtures

```text
even: (1,-4,6,-4,1)
odd:  (1,-2,0,2,-1)
```

show that the relevant seventh/ninth source derivatives change sign. Therefore

```text
positive Riesz primitive + endpoint flatness
  -> pointwise fixed-sign smoothed integrand
```

remains **DEAD**. #157 does not revive it.

## Active path

```text
PROVED THROUGH #157
  off-line zero
    -> retained regular cell-minimal first-bad certificate
    -> exact canonical source-channel energy < 0
    -> exact finite pole-prime discrepancy normal form
    -> legal production Riesz order 6
    -> complete retained Riesz-6 source-channel energy < 0

NOW — FB-04
  formulate a specific arithmetic mechanism for the EXACT complete transformed residual
  align discovery/certification tooling with the theorem-backed transformed object
  try to falsify the mechanism before theorem investment

PROMISING SUBLEAD
  expose the first Riesz boundary term
  theoremize exact leading endpoint jets only if needed
  test scalar endpoint factors across fixed cutoff cells and prime-power thresholds

THEN — FB-05
  prove an independent nonnegative theorem on the exact same retained state

TARGET
  same-state contradiction
    -> negative-root exclusion
    -> explicit outside-strip/trivial-zero seam
    -> Mathlib RiemannHypothesis wrapper
```

## Documentation authority

Current living state is maintained in:

- `research/RHRC/CURRENT_RESEARCH_PLAN.md`;
- `research/RHRC/RESEARCH_LEADS.md`;
- `research/RHRC/RESEARCH_LEADS_POST_157_PRODUCTION_RIESZ_ARITHMETIC_FRONTIER_DELTA.md`;
- `research/RHRC/OBSTRUCTION_LEDGER.md` / `DEAD_ROUTES.md`;
- `research/RHRC/DOCUMENTATION_AUTHORITY.md`;
- `research/RHRC/VALIDATION_PROTOCOL.md`;
- `research/RHRC/routes/R003_ccm_bridge/README.md`;
- `research/RHRC/control_v2/README.md`.

Older dated deltas, external reviews, countermodel reports and release audits remain historical evidence and are not rewritten to look current.

## Permanent firewalls

- RH remains OPEN.
- compiler/CI validity attaches to the exact checked object.
- theorem authority through #157 is not automatic machine claim promotion.
- a retained transformed negative certificate is not a contradiction.
- exact discrepancy/Riesz identities are not arithmetic sign theorems.
- R6 is universal on retained certificates; R8 is conditional on retained even parity.
- exact seventh/ninth leading-jet formulas remain open until separately theoremized.
- pointwise positivity of the smoothed integrand is falsified as a universal mechanism.
- interval-certified finite numerics are not Lean theorem authority.
- generic/modified-source countermodels are not zeta counterexamples.
- `D` remains algebraic, not unitary/isometric.
- negative-root exclusion is not the terminal Mathlib `RiemannHypothesis` statement without the final seam.

**RH remains OPEN.**

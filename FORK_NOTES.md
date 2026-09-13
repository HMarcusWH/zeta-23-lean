# Fork notes — current RHRC state

> **RH remains OPEN.**

## Authority snapshot

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

The validated #157 PR head and merged main are distinct commits with the same theorem tree.

## Recent theorem packages

```text
#129 source-explicit cubic defect + cross-parity secular transfer
#131 exact canonical source-moment decomposition
#134 denominator-free whole-kernel source transport
#136 absolute canonical source energy + exact channel decomposition
#137 exact source pairing + one-step determinant + sign-failure endpoint
#140-#150 regular-aperture / retained negative selected state
#152 interval-certified selected-residual falsification/certification harness
#153 retained first-bad / negative-energy certificate + exact pole-prime discrepancy
#155 discrepancy integrability + generic legal Riesz smoothing
#155 source-coordinate oddness + all even jets + even M3=0
#157 complex production D transport + production odd jets through R6/R8
#157 complete Riesz source channel + retained transformed-negative certificate
```

## What #157 adds

**PROVED:** the genuine complex production source energy satisfies the exact second-derivative centered-index transport once the complex coefficient sum vanishes; the rank-two defect is exposed and killed explicitly.

**PROVED:** boundary-flat production carriers have jets 1..6 zero; even boundary-flat carriers have jets 1..8 zero.

**PROVED:** exact complete production Riesz order 6; exact order 8 under even parity.

**PROVED:** every retained regular first-bad certificate has complete Riesz-6 source-channel energy `< 0`; the even-parity retained certificate has complete Riesz-8 energy `< 0`.

**PROVED:** a hypothetical off-line zero yields the retained Riesz-6 negative certificate.

**NOT PROVED:** an independent opposing nonnegative arithmetic sign, exact seventh/ninth leading-jet formulas, negative-root exclusion, or RH.

## Current frontier

```text
FB-01 retained whole-cell/Schur certificate                        PROVED / #153
FB-02 exact finite pole-prime discrepancy                          PROVED / #153
FB-03A finite discrepancy integrability                            PROVED / #155
FB-03B anchored primitives + AC / a.e. derivative                 PROVED / #155
FB-03C generic legal repeated IBP / conditional Riesz             PROVED / #155
FB-03D source oddness + all even jets + even M3=0                  PROVED / #155
FB-03E complex D transport + production odd jets + Riesz 6/8      PROVED / #157
FB-03F retained transformed-negative wrapper                       PROVED / #157
FB-04 complete transformed-residual arithmetic mechanism           OPEN / NOW
FB-05 scoped complete-residual nonnegative sign                    OPEN
FB-06 same-state contradiction / negative-root exclusion           OPEN
FB-07 outside-strip/trivial-zero + terminal Mathlib RH seam         OPEN
RH                                                                 OPEN
```

## Post-green clue

The next useful abstraction is likely not another restatement of the already-proved R6/R8 equality. The first nonvanishing Riesz boundary term may expose a smaller arithmetic target:

```text
E_r = E_(r+1) + boundary_term.
```

Expected leading endpoint formulas

```text
g^(7)(0) = -2*(2*pi)^6*|M3|^2
g^(9)(0) =  2*(2*pi)^8*|M4|^2
```

are **DERIVED / OPEN IN LEAN**. They must not be promoted from #157.

## Exact falsification memory

The legal boundary-flat `K=2` fixtures

```text
even: (1,-4,6,-4,1)
odd:  (1,-2,0,2,-1)
```

still kill

```text
positive Riesz primitive + endpoint flatness
  -> pointwise fixed-sign smoothed integrand.
```

This does not refute the Riesz identity. It blocks a pointwise-sign shortcut only.

## Next theorem-bearing slice after this sync

Preferred design:

```text
CCM: expose the first Riesz boundary term and probe endpoint arithmetic
```

The Lean half should prove a generic signed one-step Riesz recurrence and, only where required, exact endpoint leading-jet identities. The numerical/Arb half should immediately try to falsify any proposed scalar boundary-factor sign across fixed cutoff cells and prime-power thresholds.

If that scalar route dies, preserve the failure and return to the complete transformed residual using stationarity, lower-size transfer, whole-cell ancestry or a cancellation identity.

## Documentation state

Current living synthesis:

```text
research/RHRC/RESEARCH_LEADS.md
research/RHRC/RESEARCH_LEADS_POST_157_PRODUCTION_RIESZ_ARITHMETIC_FRONTIER_DELTA.md
research/RHRC/CURRENT_RESEARCH_PLAN.md
research/RHRC/OBSTRUCTION_LEDGER.md
research/RHRC/DEAD_ROUTES.md
```

External reviewer material remains discovery evidence unless independently reproduced or theoremized.

## Firewalls

- RH remains OPEN.
- theorem authority is through #157 only.
- machine claim promotion remains separate.
- a retained transformed negative source-channel energy is not a contradiction.
- exact Riesz 6/8 is not an arithmetic sign theorem.
- R8 is conditional on even retained parity.
- exact seventh/ninth leading-jet coefficients remain open.
- pointwise smoothed-integrand positivity remains falsified as a universal mechanism.
- the #152 harness is scoped falsification/certification infrastructure, not theorem authority.
- `D` remains algebraic, not unitary/isometric.
- negative-root exclusion is not the terminal Mathlib RH wrapper without explicit final bookkeeping.

**RH remains OPEN.**

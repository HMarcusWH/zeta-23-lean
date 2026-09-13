# RHRC — Riemann Hypothesis route-closure control plane

> **Claim firewall: RH remains OPEN.**

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
regular selected first-bad endpoint                                     PROVED / #140-#150
selected-residual falsification/certification harness                   TOOLING / #152
retained full first-bad / negative-energy certificates                  PROVED / #153
exact finite pole-prime discrepancy / full-channel normal form          PROVED / #153
finite discrepancy integrability                                        PROVED / #155
anchored Riesz primitives + AC / a.e. derivative                        PROVED / #155
generic legal repeated-IBP / conditional Riesz representation           PROVED / #155
source oddness + all even endpoint jets                                 PROVED / #155
genuine complex production D transport                                  PROVED / #157
boundary-flat jets through 6 / even jets through 8                       PROVED / #157
exact complete production Riesz 6 / even Riesz 8                         PROVED / #157
retained complete Riesz-6 negativity                                    PROVED / #157
even retained complete Riesz-8 negativity                               PROVED / #157
off-line zero -> retained Riesz-6 negative certificate                   PROVED / #157

specific complete transformed-residual arithmetic mechanism             OPEN / NOW
independent complete transformed-residual nonnegative sign               OPEN
negative-root exclusion                                                   OPEN
outside-strip/trivial-zero seam + terminal RH bridge                      OPEN
RH                                                                        OPEN
```

## Post-#157 state

The former FB-03 analytic-legality/composition frontier is closed. The project now has a theorem-backed complete transformed negative first-bad state.

The exact complete transformed channel is `canonicalRieszSourceChannelEnergy`. It preserves the Riesz-transformed pole-prime discrepancy, both reduced archimedean components and the scalar correction.

A hypothetical off-line zero therefore yields a retained regular first-bad certificate with

```text
canonicalRieszSourceChannelEnergy L 6 K x < 0.
```

This is not RH and not a contradiction. The missing theorem is an independently justified nonnegative arithmetic sign on the same forced transformed state.

## Immediate research frontier — FB-04

The next step is not another proof of transformed negativity. It is to formulate a **specific mechanism** for the complete transformed residual and try to falsify it before Lean investment.

Candidate mechanism families include:

```text
stationarity A x0=b inside the transformed representation
transfer to smaller-size good predecessor energies
whole-cell minimality across the fixed cutoff cell
first nonvanishing Riesz boundary term
exact cancellation identities coupling discrepancy/arch/scalar channels
combined-parity invariants.
```

A finite counterexample may kill an overbroad mechanism. Repeated finite success cannot prove the sign.

## Leading-jet / boundary-term lead

The post-green composition suggests exact endpoint formulas

```text
g^(7)(0) = -2*(2*pi)^6*|M3|^2
g^(9)(0) =  2*(2*pi)^8*|M4|^2.
```

**Status: DERIVED / OPEN IN LEAN.**

A promising next theorem is a generic one-step Riesz recurrence with explicit right-endpoint boundary term. This would be an integrated identity, not a pointwise-sign claim.

## Exact falsification memory

The legal boundary-flat `K=2` vectors

```text
even: (1,-4,6,-4,1)
odd:  (1,-2,0,2,-1)
```

still show the relevant seventh/ninth source derivatives change sign. Therefore

```text
positive Riesz primitive + endpoint flatness
  -> pointwise fixed-sign smoothed integrand
```

remains **DEAD**.

## Current execution priority

1. **FB-04A — boundary-term theorem/falsifier.** Expose the generic one-step Riesz boundary recurrence, theoremize exact leading jets only if required, and probe the scalar endpoint factors with exact/Arb tooling.
2. **FB-04 — mechanism falsification.** Test stationarity, lower-size transfer, boundary-term or other exact complete-residual mechanisms against canonical finite states.
3. **FB-05 — scoped sign theorem.** Prove an independent nonnegative sign on the exact retained transformed state if a mechanism survives.
4. **FB-06 — same-state contradiction.** Compose the nonnegative theorem with the #157 retained Riesz-negative certificate.
5. **FB-07 — terminal seam.** Close outside-strip/trivial-zero bookkeeping and the Mathlib RH wrapper.

Universal A4b2b domination remains a broad fallback only if a genuinely independent canonical arithmetic mechanism appears.

## Current research records

- `CURRENT_RESEARCH_PLAN.md` — execution order and theorem gates.
- `RESEARCH_LEADS_POST_157_PRODUCTION_RIESZ_ARITHMETIC_FRONTIER_DELTA.md` — newest audited post-green synthesis.
- `RESEARCH_LEADS_POST_155_RIESZ_D_TRANSPORT_FRONTIER_DELTA.md` — historical pre-#157 synthesis.
- `countermodels/POST_155_RIESZ_POINTWISE_SIGN_COUNTERMODELS_2026_09_13.md` — exact finite falsification memory for the dead pointwise-sign shortcut.
- `OBSTRUCTION_LEDGER.md` — accumulated reusable blockers.
- `DEAD_ROUTES.md` — quarantined/dead routes.
- `routes/R003_ccm_bridge/README.md` — active route theorem surface.
- `control_v2/README.md` — executable research routing.

Older dated deltas and route settlements remain historical evidence and are not rewritten to look current.

## Permanent firewalls

- RH remains OPEN.
- theorem authority is through #157; machine claim promotion remains separate.
- complete retained transformed negativity is not a contradiction without an independent nonnegative theorem.
- exact discrepancy / Riesz identities are not arithmetic sign theorems.
- R8 is conditional on even retained first-bad parity.
- exact seventh/ninth leading-jet formulas remain open until separately theoremized.
- pointwise fixed-sign smoothed-integrand positivity remains falsified as a universal route.
- external derivations and numerical experiments are not Lean authority.
- interval-certified finite numerical failures are scoped falsification evidence only.
- `D` remains algebraic, not unitary/isometric.
- terminal negative-root exclusion still needs the outside-strip/trivial-zero seam before the Mathlib `RiemannHypothesis` wrapper.

**RH remains OPEN.**

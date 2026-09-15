# RHRC obstruction-ledger delta after PR #186

> **Claim firewall: RH remains OPEN.**
>
> This delta supplements `OBSTRUCTION_LEDGER.md` with the post-#186 classification while preserving the historical ledger entries unchanged.

## Authority

```text
formal theorem authority = PR #184
validated theorem head = a756494ebe7e2530715e996b9a9a341fbe07c683
merged theorem commit = 6f04e94473eb112b59eeaa2c6fc6ac6cbe7fe30e

latest research evidence = PR #186
validated research head = 7d277a99437d98fdb7c831f25a130eac07f1b3af
merged research commit = 0494658a87d29eeb2124aa16232c264c21d23c18
research disposition = DOMINATION_SIGNAL_MIXED
```

## OBS-053 — universal production-remainder domination fails on the frozen q13/Q14 panel

**Status:** EXPERIMENTALLY FALSIFIED BROAD FORMULATION / LOCAL CONDITIONAL ROUTE REMAINS OPEN.

PR #184 proves the conditional production Schur-envelope statement

```text
P_t' = -E + R_t'
R_t' < E -> P_t' < 0.
```

PR #186 tests the corresponding physical-aperture identity on the exact frozen #180 q13/Q14 N2/K3/even schedule:

```text
P_L' = -E/L + R_L'
margin_L = E/L - R_L'
rho_L = L*R_L'/E.
```

The exact-center research certificate returns `DOMINATION_SIGNAL_MIXED`:

```text
positive margin:
  det_left_o2^-10_r2^-13
  det_left_o2^-13_r2^-16

negative margin:
  det_right_o2^-10_r2^-13
  det_right_o2^-13_r2^-16
  det_left_o2^-16_r2^-19
  det_right_o2^-16_r2^-19

unresolved primary exact centers: none
finite-width scope: FINITE_WIDTH_OUT_OF_H1_SCOPE
```

**Consequence:** do not target a theorem asserting unconditional source-specific `R_t' < E` or `R_L' < E/L` across the frozen dangerous-state class. The tested finite scope already contains certified failures.

**What remains live:** a narrower theorem of the form

```text
C(state) -> R_t' < E
```

may still matter if `C(state)` is independently meaningful, theorem-connectable, normalization-safe, and forced on the exact retained first-bad/contact state.

**Required next test:** freeze the #186 panel and search for a predeclared canonical discriminator separating the two positive-margin states from the four failures. Reject target leakage, margin-sign restatements, arbitrary normalization dependence, finite-width claims outside H1, or any condition that merely restates successor positivity.

**Permanent warning:** #186 does not falsify PR #184. #184 is conditional algebra; #186 falsifies only the broad arithmetic hypothesis that its premise holds throughout the tested frozen scope.

**No promotion:** this obstruction is research evidence, not a Lean theorem, negative-root exclusion, or RH.

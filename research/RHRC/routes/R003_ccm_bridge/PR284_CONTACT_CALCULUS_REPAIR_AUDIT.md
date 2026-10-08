# PR #284 contact-calculus repair audit

This note records the compiler-driven repair pass applied after
`f92c356ca16b1f97c6afa1413496c4c7ddd95067`.

## Repair scope

The repair sequence changes proof wiring in:

- `Zeta23/CCM/StationarySchurContact.lean`
- `Zeta23/CCM/FirstCrossingProductionResponse.lean`
- `Zeta23/CCM/FirstCrossingInheritedStationarity.lean`

The mathematical claim boundary is unchanged.

### Stationary Schur
- Makes the real scalar restriction of complex bilinear evaluation explicit.
- Converts neighborhood preimage membership to the operator-norm bound via simplification rather than a failed definitional `change`.

### Production response
- Proves `-b ∈ ker phi` directly from `inner z b = 0`.
- States normalization in the ambient Euclidean space present in the goal.

### Inherited stationarity
- Normalizes centered-extension equality before rewriting.
- Uses the current `IsLocalMin` eventual-order API.
- Composes ordinary complex-linear maps in the projected first-jet restriction.
- Uses the root `inner_map_self_eq_zero` polarization theorem.
- Derives transported-seed stationarity from the earlier-plateau non-right-crossing invariant plus exact centered energy transport, removing the invalid predecessor-dimension hop.
- Explicitly bridges the transported ambient source-matrix inequality back to the compressed quadratic form.

## Claim firewall

Formal status is determined only by the synchronized PR head and its compiler /
no-sorry / axiom / contract gates.

RH remains **OPEN**. These repairs do not upgrade the terminal claim.

## Exact-head follow-up repair (candidate)

The `cb10293e` CI cohort identified two `HasDerivAt.deriv` elaboration errors in `CanonicalCompressedApertureC2.lean` at lines 217/232.

- Carry `set_option backward.isDefEq.respectTransparency false` into the compressed calculus module, matching upstream `CanonicalFrozenApertureC2.lean`. This attempts to reconcile the different Lean instance paths (`ContinuousLinearMap.addCommGroup/module/topologicalSpace` versus `NormedAddCommGroup/NormedSpace/PseudoMetricSpace`), and is **not yet compiler-validated**.
- Preserve the exact exported derivative theorem statements and their seam-safe upstream witnesses; do not weaken them or use historical ambient-matrix derivative candidates.
- Add both derivative declarations to `#print axioms` and the R003 contract required-symbol inventory. Source-text checks do not supersede Lean compilation and full axiom auditing.

**Gate:** the new head must compile `CanonicalCompressedApertureC2`, `FirstCrossingGeneratedStrictEvenFrontier`, and `RHRC.ContactCalculusContract`, pass proof-escape/axiom/claim audits, and complete an all-workflow harvest. F04 transport, arithmetic exclusion, odd/tie branches, and RH remain OPEN.

# Dead and quarantined routes

A route is listed here when it fails for a reusable reason. Failure is a valid research output.

- **DR-001:** improve RH by a new scalar inequality consuming only the TightMult-visible single-compression statistics. Blocked by OBS-001.
- **DR-002:** fixed local-ordinal zeta mapping as a bridge from finite CCM objects to zeta zeros. Rejected in the earlier CCM campaign.
- **DR-003:** `curvature_gap` W96 as a hidden RH field. Rejected by matched adversarial null and transfer failure.
- **DR-004:** close `R001_PRIME_UPPER` by ξ-modulation averaging plus the Montgomery–Vaughan mean value ("MV gives square-root cancellation"). Rejected by exponent bookkeeping: for window `T = e^{2βa}` the provable prime-side RMS is `max(√a, e^{(1−β)a}√a)` while the depth-δ exceptional RMS is `e^{(2δ−β)a}`; detection requires `δ > 1/2` in every regime, and the dilution deficit `e^{(2δ−1)a}` is window-independent. See `routes/R001_exceptional_zero/PRIME_SIDE_FEASIBILITY_2026_08_20.md`. A revival must remove the MV additive `Σ n|c_n|²` penalty at `T ≪ X` — itself zero-density/RH-strength information.
- **DR-005:** close `R001_PRIME_UPPER` as an independent scalar arithmetic estimate at all. Blocked by OBS-008 (formal): the scalar target is a Lean-proved equivalent of RH, so "apply PNT harder" cannot terminate the route.
- **DR-006:** three R002 observable families, killed in `routes/R002_multi_probe/MULTI_PROBE_GRAM_OPERATOR_FEASIBILITY_2026_08_21.md`.
  - *R002-B, odd moment `tr G̃³`*: the bulk is `≍ N λ^{-3}` with `N ≍ Tl/2π` while a visible negative eigenvalue moves the cubic by `O(1)`; detection needs the cubic main term to relative precision `1/N`, i.e. a power-saving asymptotic for the ternary correlation `Σ Λ(n)Λ(m)Λ(l)(nml)^{-1/2}W` on the near-multiplicative diagonal `l ≈ nm`. No unconditional mechanism at that strength; the two proven moments do not extend to the third.
  - *R002-E, L² aperture coherence*: collapses to OBS-008. `paperFT`/`weilZeroFilter`/`literatureRHS` are linear in the test, so the matrix `G_ij(A) = (1/A)∫F_i conj(F_j)` is exactly the scalar family over the probe span; and L²-subexponentiality still gives Laplace holomorphy on `Re z > 0` (split into unit blocks, Cauchy–Schwarz), so the `ExposedPole` contradiction runs verbatim and the property is RH-equivalent. Its arithmetic side is the DR-004 wall.
  - *R002-F, full-diagonal majorization*: the retained diagonal `{m_j‖v_j‖²}` is δ-insensitive at leading order — `‖v_j‖²` is pinned by the frame identity `Σ_k φ̂(γ−τ_k)² = aL²` independently of `δ`.
  A revival of B needs ternary-correlation technology that does not exist; a revival of E needs an escape from OBS-008 that is not a repackaging; a revival of F needs a δ-sensitive diagonal functional.

Do not silently resurrect a dead route. A revival must state which blocking premise has changed.

# PR #42 continuation checkpoint — 2026-08-25

Production branch `research/r003-deterministic-rhs-completion` is pushed and clean at `8ed0517`.

Green production checkpoints:

- `781af47`: exact literature-channel source bridge `dictionaryArchRHS_sourceTest`.
- `87d9966`: off-diagonal arch theorem `dictionaryArchRHS_basis_of_ne` and required full-mu integrability.
- `6fb03d3`: quarter-digamma value and `two_pi_mul_mu_zero`.
- `8e5d4e8`: both diagonal reference improper-integral value/integrability pairs and exact `mu_zero_reference_tail_eq_neg_two_wCorrection`.
- `8ed0517`: square-root-weighted diagonal Fourier L1, `integrable_paperFT_dictionaryBasisTest_diag_mul_mu_sub_mu_zero`, and full `integrable_paperFT_dictionaryBasisTest_diag_mul_mu`.

The WIP branch stores two non-production drafts:

- `handoff/diagonal_design/Probe.lean`: Phase F diagonal continuation.
- `handoff/finite_lift_design/Probe.lean`: Phases H-J candidate through the exact advertised endpoint.

Immediate next compiler action:

1. Resume from the production SHA above.
2. The weighted block is already in production. The next known errors start in the physical diagonal bridge near line 866 of the diagonal draft.
3. Land/push the physical diagonal equality, then export the Phase-G pair:
   - `integrable_paperFT_dictionaryBasisTest_mul_mu`
   - `dictionaryArchRHS_basis`
4. Compile the H-J draft only after those two exports exist. It preserves prime truncation before finite coefficient reordering and ends at `literatureRHS_dictionaryTest_eq_quadraticForm`.

Pinned local toolchain:

- `ELAN_HOME=C:\Users\macka\Documents\Codex\2026-08-24\the-other-documents-are-for-history\work\elan`
- Lake executable: `C:\Users\macka\Documents\Codex\2026-08-24\the-other-documents-are-for-history\work\elan\bin\lake.exe`

After the exact endpoint is green: update `ClaimBindings.lean`, change only `R003_CCM_RHS_IDENTITY` to `PROVED_UNCONDITIONAL`, delete/cover `DictionaryArchSourceSeries.lean`, run full settlement checks, verify the generated merge ref, and resolve the five review threads with theorem/SHA evidence. Keep RH OPEN and retain `dictionaryMatrix = finiteMatrix + 2*cCorrection*I`.

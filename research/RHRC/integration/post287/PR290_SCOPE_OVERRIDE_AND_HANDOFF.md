# PR #290 repair-only merge-scope authorization and next-PR handoff

**Authority:** user instruction on 2026-10-13: complete repairs, generated-state synchronization, reproducibility, documentation, and validation in PR #290; merge only after user's separate merge decision. Complete the K3 even/odd finite-window mathematics in a **new PR**.

**Original rev4 remains intact.** `requirements.D2=FULL_K3_BOTH_PARITIES_CONTINUOUS_[1/512,log16]` is not weakened as a mathematical statement, never claimed proved, and remains an OPEN requirement. The **merge acceptance scope** of PR #290 alone is changed to `REPAIR_ONLY_D2_DEFERRED`. The original `BUILD_CONTRACT.md` and frozen methods remain historical. The next PR must explicitly resolve D2 or give a new independently reviewed method/disposition.

## Source-pinned guarded evidence (not current-head Lean proof terms)

- Guarded source: `31512dbb698dd59b90cfa32549f0e9273a5163f9`, manual workflow [38332529352](https://github.com/HMarcusWH/zeta-23-lean/actions/runs/38332529352).
- 34 manual jobs: 32 executed successfully, 2 skipped. In the K3 campaign, 30/30 layer artifacts received; 26 were complete checked positive layers, four were checked partial layers; zero missing and zero unverified layer payloads. The independent global assembler returned `UNRESOLVED` — **no** complete non-partial global K3 check passed.
- Even Q9: 4,941 accepted rational intervals, 7 unresolved subintervals.
- Even Q13: 6,051 accepted, 7 unresolved.
- Even Q14: 4,302 accepted, 11 unresolved.
- Even Q15: 4,208 accepted, 10 unresolved.
- All 15 odd-sector and 11 other even-sector layers passed their defined finite interval check. Total unresolved **35** subintervals in four even layers; `UNRESOLVED` does not assert a negative zeta eigenvalue.
- K2-even guarded M51 replay: 1,310 accepted intervals, 192-bit independent checker, rational endpoint above the true `log 16`. K2-odd guarded prerequisite: 350 intervals, 192-bit independent checking. Numerically checked source identities stay on their original run/commit.
- Q14 frozen SECOND feasibility gate: 18/18 boxes PASS under corrected finite guards at 384 bits. This is **not** a full K3 window. The predeclared FOURTH fallback was not attempted and is permitted only when the *frozen* SECOND gate is UNRESOLVED; partial full-window tiles alone do not license switching representation.
- Earlier centre-only `Delta''` and `min(0,nan.lower())` certificates remain **invalidated**, never reinstated.

## Provenance and migration

The guarded run was on `31512dbb`, not PR #290's subsequently revised head. `post287/certificate_integrity.py` hashes its complete `SOURCE_INPUTS` list, including the legacy M51 display script, and records `git rev-parse HEAD`. The later legacy-script change is audited as display-only (see `LEGACY_M51_DISPLAY_SOURCE_EQUIVALENCE.md`), but does **not** permit mutating old artifact source-digest fields or claiming a current-head rerun. Reuse archival evidence with its original SHA/manifest/precision, not as unconditional Lean `hM51` or `hWindows` proofs.

## Forward obligation

Next PR must start from the source-bound accepted and unresolved rational intervals and target the four even-sector cells Q9/Q13/Q14/Q15. New derivative order, interval budget, or source representation requires a **new predeclared independent method contract**, not silent retroactive fitting. The separate strict-odd and parity-tie **selected-ground** adapters are not the same mathematical question as K3 finite-window parity coverage.

## Merge decision

PR #290 is a supporting-theorem, research-evidence, graph-integrity and CI repair milestone. It may be presented for the **user's explicit merge approval** after the exact integration tree, clean-checkout graph, Lean/axiom/no-placeholder and source-fidelity gates pass. Neither D2 Full, Step 4 exclusion nor RH is claimed proved. **RH_OPEN.**

# Legacy M51 display-only source-equivalence audit

Date: 2026-10-13. Terminal claim: **RH_OPEN**. This is a source-equivalence
receipt, not a new numerical certificate or Lean theorem.

The corrected file is
`research/RHRC/routes/R003_ccm_bridge/post285/post285_m51_k2_even_bottom_certificate.py`.
The comparison source is exact archived commit
`31512dbb698dd59b90cfa32549f0e9273a5163f9`; it was still unchanged at pre-edit head
`a7e4e8e55ffb71799d7862be0496082ee2983af9`.

Only displayed scope changed: the module documentation now says `[1/400, U]`,
`U = 2772588722239781/10^15 < log 16`, with `(U, log 16]` OPEN; the erroneous
comment claiming `LOG16_UP >= log 16` is corrected; and `main` prints this
rational scope rather than claiming coverage to exact `log 16`.

| Canonical Linux/Git LF identity | Archived source | Candidate source |
|---|---|---|
| Git blob | `66d149e9d08f19eaa79196dee5cae75d73041b74` | `505636e356836db71dafe3a03a53f59708aae6b2` |
| SHA256 | `59c3bb47d966449bdc267a7413e3d67ed0c872a8cae3e578e87a75bb8133e70b` | `3dc045594d5236420452ece91f56482e1c0b680eaa470369687beecfdec6abf9` |

The whole-file digest therefore intentionally changes for **one of the 28**
manual-campaign inputs. Comparing canonical file bytes against archived
31512dbb confirmed the other 27 are exactly identical. Windows CRLF working
hashes are recorded separately in the
[machine-readable receipt](LEGACY_M51_DISPLAY_SOURCE_EQUIVALENCE.json); they
are not substituted for the canonical LF identities above.

AST comparison confirms all nine helper functions are identical, including
their docstrings: `ball`, `cell_bounds`, `cover`, `lam_point`,
`legal_even_carrier`, `lower_bound`, `physical_V`, `quad`, and
`refine_minimum`. All imports and all top-level assignments are identical,
including `LOG16_UP`, precision, carrier coefficients and subdivision depth.
After restoring just the module docstring and the one changed `statement`
literal, the entire module AST is identical. Thus `main` has the same
computations, control flow, schedules, acceptance logic and exit status; only
its report wording differs. No algorithm or numerical result was changed.

The active manual 31512dbb campaign and all old receipts must retain their
original exact commit, source digests and raw output bytes. This correction
does not invalidate the guarded archived calculation, change its source in
place, or authorize silent digest substitution. It also does not upgrade old
invalid unguarded receipts or discharge the legacy exact-log16 gap. Any final
candidate-source acceptance must be separately bound and checked; this audit
alone is not a fresh checker receipt.

Validation used syntax/AST comparison, exact source-byte/digest comparison,
the post285 ledger check and whitespace review. No numerical experiment or
certificate replay was run in this display-only migration.

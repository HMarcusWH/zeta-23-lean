# R003 CCM normalization audit — 2026-08-21

Status: **reference/formula audit passed; no mathematical claim promoted**.

This note records the correction introduced after comparing the fork-owned finite CCM matrix against the cutoff-free Connes--van Suijlekom / Connes--Consani--Moscovici implementation shipped with Akiva Groskin's finite Guinand--Weil dictionary package.

## Why this audit came before the old PR #33 roadmap

PR #32 planned to prove directly

```text
EF.literatureRHS(K_nm) = 2*M_nm + 4*cCorrection(L)*delta_nm.
```

That target was based on the fork's own finite explicit-formula diagnostic. After reading the July 2026 finite-dictionary paper and pinning its verification code, it became necessary to separate three conventions:

```text
M        fork-owned formal CCM matrix
Q_inf    cutoff-free CvS/CCM Galerkin matrix in Groskin's dictionary
WeilGram inherited explicit-formula matrix normalization used by R003
```

The normalization audit therefore precedes any new Lean bridge proof.

## Identified reference relation

Across `c in {4,9,13,25,29,100}` and centered indices `-2..2`, the independent closed-form source implementation gives

```text
Q_inf(n,m) = M(n,m)                         for n != m
Q_inf(n,n) = M(n,n) + 2*cCorrection(L)     for n = m
```

or

```text
Q_inf = M + 2*cCorrection(L)*I.
```

The maximum residual after this correction is at double-roundoff scale in the audit grid. Primitive comparison localizes the convention difference further:

```text
alpha_reference = alpha_ours
beta_reference  = beta_ours
gamma_reference = gamma_ours - cCorrection(L)
pole_reference  = pole_ours
```

### Lock versus reproducible audit output

`CCM_NORMALIZATION_LOCK_v1.json` is the **curated, reviewed route lock**. It freezes provenance, the source commit/blob identities, the summarized convention map, the merge gate, and the explicit non-claims. It is not a generated scratch artifact.

`compare_ccm_normalizations.py` instead writes a detailed reproducibility artifact using schema `CCM_NORMALIZATION_AUDIT_v1`; by default it writes

```text
CCM_NORMALIZATION_AUDIT_latest.json
```

and it deliberately refuses to overwrite `CCM_NORMALIZATION_LOCK_v1.json` even if that path is supplied explicitly. CI writes the same detailed audit to a temporary path and checks only its exit status.

To rerun the audit locally:

```bash
python research/RHRC/routes/R003_ccm_bridge/compare_ccm_normalizations.py
```

To refresh the curated lock, first rerun and inspect the detailed audit, then update the lock deliberately in a reviewed commit. Do not treat the runtime artifact as a byte-for-byte lock generator.

## Reconciliation with PR #29

PR #29's finite diagnostic found

```text
WeilGram = 2*M + 4*cCorrection(L)*I.
```

Combining that diagnostic with the independent cutoff-free CCM audit gives the convention reconciliation

```text
WeilGram = 2*Q_inf.
```

This is the current **normalization target**, not a promoted theorem. It explains why PR #29 saw both a factor two and a diagonal correction while Groskin's Lemma 2.1 describes an entry-level identification with the CCM Galerkin matrix: the two statements are using different matrix normalizations, and the fork-owned `M` also carries a diagonal `cCorrection` convention relative to `Q_inf`.

## Immediate consequence for the build order

The old transform-first PR #33 sequence is **superseded**. The route SSOT is now the active sequence in `research/RHRC/routes/R003_ccm_bridge/README.md`.

The revised sequence is:

1. **PR #33** — keep this PR reference-only and freeze the external provenance + normalization lock;
2. **PR #34** — factor the generic divided-difference/source calculus in Lean;
3. **PR #35** — formalize the finite dictionary objects and source transport;
4. **PR #36** — choose and prove the shortest admissibility bridge (broaden EF to Groskin's admissible class or use the existing C2 mollifier adapter);
5. **PR #37** — prove the exact finite zero-side/CCM bridge in the now-locked normalization.

The old scalar-shift, transform, prime/pole, archimedean, and mollifier analyses remain useful proof material and fallback lemmas. They are no longer the active PR ordering and must not be read as authorization to restart the pre-literature transform-first sequence.

## Authority boundary

- `research/RHRC/external/connes_cvs/*`: external reference/oracle only.
- `compare_ccm_normalizations.py`: falsification and normalization audit only.
- `CCM_NORMALIZATION_LOCK_v1.json`: curated route lock/provenance only.
- `CCM_NORMALIZATION_AUDIT_latest.json`: generated local audit artifact; not theorem authority and not required to be committed.
- `Zeta23.CCM` + comparator: theorem authority.

RH remains open. `R003_CCM_BRIDGE` remains open.

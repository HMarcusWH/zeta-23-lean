# R003 CCM normalization audit — 2026-08-21

Status: **reference/formula audit passed; no mathematical claim promoted**.

This note records the correction introduced after comparing the fork-owned finite CCM matrix against the cutoff-free Connes--van Suijlekom / Connes--Consani--Moscovici implementation shipped with Akiva Groskin's finite Guinand--Weil dictionary package.

## Why this audit came before the old PR #33 roadmap

PR #32 planned to prove directly

```text
EF.literatureRHS(K_nm) = 2*M_nm + 4*cCorrection(L)*delta_nm.
```

That target was based on the fork's own finite explicit-formula diagnostic.  After reading the July 2026 finite-dictionary paper and pinning its verification code, it became necessary to separate three conventions:

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

The maximum residual after this correction is at double-roundoff scale in the audit grid.  Primitive comparison localizes the convention difference further:

```text
alpha_reference = alpha_ours
beta_reference  = beta_ours
gamma_reference = gamma_ours - cCorrection(L)
pole_reference  = pole_ours
```

See `CCM_NORMALIZATION_LOCK_v1.json` and regenerate with `compare_ccm_normalizations.py`.

## Reconciliation with PR #29

PR #29's finite diagnostic found

```text
WeilGram = 2*M + 4*cCorrection(L)*I.
```

Combining that diagnostic with the independent cutoff-free CCM audit gives the convention reconciliation

```text
WeilGram = 2*Q_inf.
```

This is the current **normalization target**, not a promoted theorem.  It explains why PR #29 saw both a factor two and a diagonal correction while Groskin's Lemma 2.1 describes an entry-level identification with the CCM Galerkin matrix: the two statements are using different matrix normalizations, and the fork-owned `M` also carries a diagonal `cCorrection` convention relative to `Q_inf`.

## Immediate consequence for the build order

Do **not** begin the old transform-first PR #33 until this convention map is treated as the object to prove.

The revised sequence is:

1. keep this PR reference-only and freeze the external provenance + normalization lock;
2. factor the generic divided-difference/source calculus in Lean;
3. formalize the finite dictionary objects and source transport;
4. choose the shortest admissibility bridge (broaden EF to Groskin's class or use the existing C2 mollifier adapter);
5. prove the exact finite zero-side bridge in the now-locked normalization.

The old scalar-shift analysis remains useful, but it should be interpreted as the conversion from fork/inherited-EF conventions to the cutoff-free CCM convention rather than as an unexplained new zeta structure.

## Authority boundary

- `research/RHRC/external/connes_cvs/*`: external reference/oracle only.
- `compare_ccm_normalizations.py`: falsification and normalization audit only.
- `CCM_NORMALIZATION_LOCK_v1.json`: route lock/provenance only.
- `Zeta23.CCM` + comparator: theorem authority.

RH remains open. `R003_CCM_BRIDGE` remains open.

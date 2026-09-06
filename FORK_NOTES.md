# Fork notes — current RHRC state

> **RH remains OPEN.**

## Authority snapshot

```text
live main after PR #119 = d4175d2bb305e62863f593824b3f40e921a46ee6
live main tree = 1985472ac470822af279044261fa365fb9bb5535

theorem-state anchor = PR #119 merge d4175d2bb305e62863f593824b3f40e921a46ee6
theorem tree = 1985472ac470822af279044261fa365fb9bb5535
FIRST-BAD-RIGIDITY-E3-A exact secular equivalence = PROVED / MERGED

control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
Control v2 / FFBBP v1.6 hardened state = MERGED GREEN CONTROL INFRASTRUCTURE

RH = OPEN
```

Live GitHub head + Lean/compiler/CI remain authoritative. PRs #118/#119 advance theorem authority only; the latest merged Control-v2 change remains #117.

## Recent theorem packages

```text
#94  F1 canonical finite negative obstruction
#96  constrained canonical algebra
#98  Euclidean constrained sector
#100 exact centered N-flow + fixed-L negative tail
#102 exact reversal symmetry + even commutator collapse
#103 exact parity geometry + algebraic D-equivalence
#105 least bad parity size + 1d successor shell
#107 parity compression + genuine negative eigenmode + non-inheritance
#109 nonzero shell projection + exact parity normals + KKT
#110 cubic parity channel + rank-at-most-one compressed parity defect
#112 global first bad + intrinsic shell + exact cubic factorization
#113 intrinsic direct sum + shifted inverse + scalar Schur identity
#115 canonical cubic shell incidence in both parity carriers
#118 canonical cubic quotient coordinate + normalized Schur
#119 exact canonical secular root/eigenmode equivalence
```

## Current frontier

```text
FIRST-BAD-RIGIDITY-E
  E1    cubic-shell incidence                                      PROVED / #115
  E2    canonical cubic coordinate + normalized Schur              PROVED / #118
  E3-A  exact quotient-secular root <-> negative-shift eigenmode   PROVED / #119

  E3-B  projected symmetry + shifted coercivity/resolvent          NOW
        + pointwise bridge to the explicit Schur scalar
        + theorem-backed one-step bound if the metric package closes

  E4    parity nullity + zero-resonance / kernel-coupling          PARALLEL / NEXT

  E3-C  resolvent monotonicity / root uniqueness                   AFTER E3-B/E4
        root exclusion remains a separate stronger target

PARALLEL
  deformation-budget gap/coupling/summability falsifiers
  G1-B1B -> G1-final -> S-NEG -> G23
```

## What #118/#119 changed

#118 removed arbitrary shell scaling. The canonical cubic shell vector now supplies the faithful coordinate on the one-dimensional new N-flow quotient, and a genuine negative eigenmode can be normalized so its shell part is exactly that vector.

#119 then constructs, for every safe `lam<0`, the canonical shifted-resolvent trial vector and full eigenvalue residual. The residual has zero predecessor coordinate, so its canonical cubic quotient coordinate vanishes exactly when the whole residual vanishes. Therefore

```text
cubicSecularScalar(lam)=0
  <-> exists nonzero v with T v = lam v.
```

This is a genuine two-way spectral reduction, but not root exclusion.

## Important post-#119 correction

The exact #119 `cubicSecularScalar` is defined as the quotient coordinate of the **full residual**. The older #113/#118 expression

```text
<Tc,c> - lam<c,c> - <R_lam Bc,Bc>
```

is theorem-backed on actual eigenmodes, but its pointwise equality to the #119 scalar for arbitrary safe negative shifts is not yet theoremized.

That bridge belongs in E3-B. Do not prove sign/monotonicity results for one representation and silently transfer them to the other.

## Zero-resonance warning

At a global first bad state the predecessor block is nonnegative, not known strictly positive. Hence `ker A` may be nontrivial and `R_lam=(A-lam I)^(-1)` may blow up as `lam -> 0-`.

This promotes the E4/kernel question from a secondary parity curiosity to a direct part of the first-bad rigidity problem. A high-value test is whether the canonical coupling `b=Bc` annihilates `ker A`; alternatively a nonzero resonant coupling may itself enforce a useful asymptotic constraint.

## Post-#119 strategic composition

```text
#119 exact secular equivalence
  -> E3-B projected symmetry / coercivity / explicit Schur bridge
  -> theorem-backed quantitative one-step displacement
  + E4 zero-resonance/nullity structure
  -> E3-C monotonicity / root-count control if justified
  -> CCM-specific negative-root exclusion attempt
```

The deformation-budget lane should continue to probe

```text
g_N = q_N-mu_N
beta_N
beta_N^2/g_N
```

but only theorem-backed E3 estimates may turn those diagnostics into proof ingredients. A fitted or finite tail remains non-authoritative.

## Firewalls

- RH remains OPEN.
- D is algebraic, not unitary/isometric.
- exact cubic factorization does not prove exact rank one.
- nonzero shell coordinate does not imply pure shell behavior.
- no shell invariance is proved.
- `A-lam I` is safe only for `lam<0`; no `A^-1` at zero.
- predecessor nonnegativity does not imply a spectral gap.
- #119 root equivalence does not imply root absence.
- root uniqueness, if proved, would still not imply positivity.
- no source-normalization or claim-registry change follows from #118/#119.
- positivity / finite-to-infinite closure / RH remain OPEN.

Current research detail: `research/RHRC/RESEARCH_LEADS_POST_119_DELTA.md`.

**RH remains OPEN.**
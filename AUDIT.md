# RHRC formal audit — theorem authority through PR #119; control authority through PR #117

> **RH remains OPEN.**

## Current authority split

```text
live main after #119 = d4175d2bb305e62863f593824b3f40e921a46ee6
live main tree = 1985472ac470822af279044261fa365fb9bb5535

theorem-state anchor = PR #119 merge d4175d2bb305e62863f593824b3f40e921a46ee6
theorem tree = 1985472ac470822af279044261fa365fb9bb5535
theorem-bearing merged through = PR #119
FIRST-BAD-RIGIDITY-E3-A exact canonical secular equation = PROVED / MERGED

control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
Control v2 / FFBBP v1.6 hardened research-control state = MERGED GREEN CONTROL INFRASTRUCTURE

RH = OPEN
```

Live GitHub head + exact compiler/CI evidence outrank this prose. PRs #118/#119 changed theorem files and umbrella imports; they did not alter Control-v2 semantics or terminal RH authority.

## PR #112 — FIRST-BAD-RIGIDITY-D1

**PROVED:** global first badness; both predecessor parities nonnegative below the first bad size; intrinsic predecessor `W`; intrinsic one-step shell `S` with `finrank S=1`; predecessor plus shell spanning; first-bad negative eigenmode with nonzero shell content; exact cubic factorization of the parity defect; ExceptionalZero packaging at one common finite state.

## PR #113 — FIRST-BAD-RIGIDITY-D2

**PROVED:** canonical complementary decomposition `V=W⊕S`; canonical predecessor/shell projections; predecessor/shell orthogonality; projected predecessor block `A=P_W T|_W`; shell coupling `B=P_W T|_S`; predecessor nonnegativity descends to `A`; for every real `lam<0`, `A-lam I` is bijective; canonical shifted resolvent; predecessor reconstruction; basis-free shifted Schur identity.

**Not proved:** shell invariance, `A^-1` at zero, strict predecessor positivity, root exclusion, RH.

## PR #115 — FIRST-BAD-RIGIDITY-E1

**PROVED:** parity-uniform canonical cubic successor direction is not inherited from the predecessor; `intrinsicCubicShellPart p N != 0` in the stated nontrivial range; the same global first-bad state forced by an off-line zero carries both a nonzero negative-mode shell coordinate and a nonzero canonical cubic shell coordinate.

## PR #118 — FIRST-BAD-RIGIDITY-E2

**PROVED:**

- canonical complex coordinate `intrinsicCubicShellCoordinate` on the one-dimensional shell;
- exact shell reconstruction from that coordinate;
- coordinate zero iff shell vector zero;
- canonical quotient coordinate on the successor with kernel exactly the predecessor;
- canonical successor cubic vector has quotient coordinate one;
- on the odd carrier the exact cubic parity-defect functional equals the canonical quotient coordinate of the exact intertwining defect;
- every genuine negative first-bad eigenmode has nonzero cubic quotient coordinate;
- canonical whole-eigenvector normalization with shell part exactly `intrinsicCubicShellPart`;
- canonical cubic-shell shifted Schur identity.

**Deliberately not proved by #118:** shell invariance, D-unitarity, nonzero defect functional on a specific vector, exact defect rank one, secular converse, sign/monotonicity, positivity closure, RH.

## PR #119 — FIRST-BAD-RIGIDITY-E3-A

Exact theorem head: `2c18909710d9dab0a111849a7c6160be8736e541`.

Merged main: `d4175d2bb305e62863f593824b3f40e921a46ee6`.

**PROVED:**

1. the shifted predecessor resolvent is a right inverse as well as the previously available inverse structure;
2. canonical trial vector at every safe negative shift

   ```text
   u_lam = -(A-lam I)^(-1) Bc + c;
   ```

3. exact predecessor and shell coordinates of that trial vector;
4. trial vector quotient coordinate is one and hence the trial vector is nonzero;
5. full eigenvalue residual

   ```text
   r_lam = T u_lam - lam u_lam;
   ```

6. `intrinsicPredecessorPart r_lam = 0`;
7. canonical secular scalar

   ```text
   cubicSecularScalar(lam) = intrinsicCubicQuotientCoordinate(r_lam);
   ```

8. exact scalarization

   ```text
   cubicSecularScalar(lam)=0 <-> r_lam=0;
   ```

9. exact trial eigenmode criterion;
10. any genuine negative eigenmode canonically normalizes to the same trial vector;
11. main E3-A theorem

   ```text
   cubicSecularScalar(lam)=0
     <-> exists nonzero v, parityCompressedCanonical v = lam • v;
   ```

12. ExceptionalZero endpoint: a hypothetical off-line zeta zero forces one global-first-bad finite state carrying an exact negative root of this secular scalar and the root/eigenmode equivalence at that same shift.

**Critical claim boundary:** the #119 scalar is the canonical quotient coordinate of the full residual. The older #113/#118 explicit Schur expression is theorem-backed on actual eigenmodes, but its pointwise identity with `cubicSecularScalar` for arbitrary safe negative shifts is not yet formalized.

## PR #117 — latest control-plane authority

**CI-VERIFIED CONTROL INFRASTRUCTURE:** Control-v2 hardening, typed deformation-budget steps, horizon-certificate requirement, decision-commutation checks, archaeology-path binding, deterministic routing transparency, theorem/control anchor separation.

PR #117 changed no `Zeta23/**/*.lean` theorem declaration and does not alter mathematical authority beyond the theorem anchor current at its own merge. After later #118/#119 theorem merges, the separate control-plane anchor remains #117.

## Current formal state

```text
least/global bad + predecessor nonnegative + 1d shell                 PROVED
negative parity-compressed eigenmode                                  PROVED
exact KKT / cubic one-channel factorization                           PROVED
canonical V=W⊕S                                                       PROVED
safe shifted predecessor resolvent for lam<0                          PROVED
canonical cubic shell coordinate / quotient                           PROVED / #118
canonical negative-mode normalization                                 PROVED / #118
exact quotient-secular root <-> eigenmode                              PROVED / #119
off-line zero -> same global-first-bad negative secular root          PROVED / #119

projected predecessor block symmetric                                 DERIVED / OPEN FORMALIZATION
quantitative shifted coercivity / resolvent norm bound                DERIVED / OPEN FORMALIZATION
resolvent quadratic realness / positivity                             DERIVED / OPEN FORMALIZATION
#119 scalar = normalized explicit Schur scalar                         DERIVED / OPEN FORMALIZATION
quantitative predecessor-floor one-step inequality                    LEAD / OPEN FORMALIZATION
parity shifted-nullity difference <=1                                 DERIVED / OPEN FORMALIZATION
zero-resonance / kernel-coupling classification                       OPEN
resolvent monotonicity / root uniqueness                              OPEN
negative-root exclusion                                               OPEN
positivity / finite-to-infinite closure                               OPEN
RH                                                                     OPEN
```

## Current research frontier

### E3-B — metric bridge

The next theorem layer should stay on the already-defined native objects:

- prove `intrinsicPredecessorBlock` symmetric from full parity-compression symmetry plus predecessor/shell orthogonality;
- prove quantitative coercivity of `A-lam I` for `lam<0`;
- derive a safe resolvent norm estimate;
- prove resolvent symmetry and real/nonnegative quadratic values;
- identify the #119 quotient-coordinate secular scalar with the normalized explicit Schur expression.

Only after that pointwise bridge is theoremized should sign or monotonicity claims be attached to the #119 secular scalar.

### E4 — zero resonance / parity nullity

Global-first-bad supplies `A>=0`, not `A>0`. A nontrivial `ker A` can make `(A-lam I)^(-1)` singular as `lam -> 0-`. This is now a direct first-bad obstruction, not a side issue.

The high-value questions are:

```text
Does Bc annihilate ker A?
```

and

```text
Can the rank-at-most-one parity defect theoremize a shifted-nullity difference <=1?
```

Both remain OPEN until separately proved.

## Permanent firewalls

- compiler/CI validity is authoritative; repository presence alone is not;
- supporting theorem checks do not automatically imply machine claim promotion;
- `V=W⊕S` does not imply shell invariance;
- D is algebraic, not unitary/isometric;
- exact cubic factorization does not imply exact nonzero rank one;
- predecessor nonnegative does not imply a positive spectral gap;
- never replace `(A-lam I)^(-1)` for `lam<0` by `A^-1` at zero;
- #119 secular equivalence is a reduction, not a contradiction;
- pointwise equality between quotient and explicit Schur scalar remains to be proved;
- root uniqueness, if later obtained, would not imply root absence;
- no finite/fitted deformation tail is a complete proof certificate;
- no source-normalization, promoted-binding, positivity, finite-to-infinite or RH change is implied by #118/#119.

Detailed current post-green implications: `research/RHRC/RESEARCH_LEADS_POST_119_DELTA.md`.

**RH remains OPEN.**
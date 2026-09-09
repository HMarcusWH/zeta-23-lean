# RHRC current research plan

> **Claim firewall: RH remains OPEN.**

## Current authority split

```text
live main after theorem PR #137 = fa2f209a6eb8b4059968e8d61239d80588ca256c
live main tree = e3de4dc0377f0124832822b6f97ab5bbd7718640

theorem-state anchor = PR #137 merge fa2f209a6eb8b4059968e8d61239d80588ca256c
validated theorem head = 64988e142590c82bd0ad43604279ede9a8e85eff
theorem tree = e3de4dc0377f0124832822b6f97ab5bbd7718640
theorem-bearing merged through = PR #137
RHRC #878 = SUCCESS
Permansson #651 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

Live GitHub head + exact Lean/compiler/CI remain authoritative. Machine claim promotion is separate.

## One-screen frontier

```text
DONE
  finite legal off-line-zero reduction
  canonical finite negative obstruction
  exact centered N-flow / parity / first-bad / KKT / one-dimensional shell
  exact shifted and zero-shift Schur machinery
  exact cross-parity source transfer
  exact pole/arch/prime source-moment decomposition / #131
  exact denominator-free zero-shift kernel/source transport / #134
  scalar-sensitive absolute canonical source energy / #136
  exact production source pairing / #137
  exact one-step determinant Δ(w) / #137
  domination -> kernel annihilation -> zero-shift preimage / #137
  domination + predecessor nonnegativity -> Re S0>=0 / #137
  domination -> no safe negative explicit Schur root / #137
  off-line zero -> global-first-bad domination failure / #137
  off-line zero -> q_c<0 OR exists w, Δ(w)<0 / #137

POST-#137 RESEARCH CONCLUSION
  the absolute-energy object is built
  the sufficiency theorem is built
  the global countercertificate is built
  the remaining content is the canonical arithmetic sign theorem itself
  generic structural/factorwise/shift-blind routes remain quarantined
  the determinant reduction is exact but may be essentially equivalent to
  one-step block positivity under predecessor nonnegativity

NOW — A4b2b: CANONICAL SHELL / DETERMINANT SIGN THEOREM
  under the exact first-bad-compatible hypotheses prove

    q_c = cubicShellRealEnergy p L N >= 0
    cubicOneStepDeterminant p L N w >= 0 for every predecessor w

  prove this from the actual canonical pole/arch/scalar/prime source.
  do not assume `canonicalOneStepDomination` as a helper.

FIRST FALSIFICATION GATE
  search exact/symbolic or rigorously enclosed low-dimensional canonical states
  satisfying the relevant predecessor nonnegativity hypotheses for

    q_c < 0
    or
    Δ(w) < 0.

  A canonical witness kills this route, not RH.

STRUCTURE GATE
  before a long inequality proof, look for one of:

    full-source Gram representation
    integral positivity representation
    Cauchy-Schwarz remainder identity for Δ
    sum-of-squares factorization
    exact cancellation reducing Δ to a smaller positive kernel

  Individual source atoms are indefinite, so termwise positivity is not the default plan.

QUANTITATIVE LANE
  retarget boundary-flat source-coordinate cancellation to q_c and Δ:

    candidate orders omega^7 / omega^9 remain DERIVED / EXPERIMENTAL

  formalize them only if they give a rigorous bound on the full-source determinant.

OPTIONAL / FALLBACK — A4R REGULAR-APERTURE SELECTION
  use only if it materially simplifies the source sign proof.
  Positive-definite predecessors are not negative-root exclusion.
  #137 already proves domination would remove resonance without A4R.

PARALLEL
  E4-B shifted-nullity
  E3-C secular monotonicity/root-count control
  E3-B3 lower-floor deformation
  deformation-budget diagnostic

  These remain lower priority unless they add independent source-specific exclusion information.

TARGET
  canonical shell/determinant signs
  -> canonicalOneStepDomination at every forced first-bad state
  -> contradiction with #137 off-line-zero -> domination failure
  -> no off-line zero through existing reduction
  -> explicit terminal Mathlib RiemannHypothesis wrapper
  RH OPEN
```

## Exact #136/#137 theorem objects now available

### Scalar-sensitive energy

`CanonicalSourceEnergy.lean` exposes:

```text
matrixRealEnergy
parityCanonicalSourceEnergy
canonicalSourceChannelEnergy
cubicShellRealEnergy
```

with exact pole/arch/scalar/prime decomposition and exact zero-shift trial-energy bridge.

### Complex pairing

`CanonicalSourcePairing.lean` extends the bookkeeping from self-energy to the exact complex pairing needed for the shell/predecessor cross term.

### One-step determinant

`CanonicalOneStepDomination.lean` exposes:

```text
intrinsicPredecessorRealEnergy
cubicShellCoupling
cubicOneStepDeterminant
canonicalOneStepDomination
```

and the exact channel formula for the determinant.

### Global countercertificate

`GlobalFirstBadOneStepDomination.lean` proves that a hypothetical off-line zero forces

```text
q_c < 0 OR exists w, Δ(w) < 0
```

at one global-first-bad predecessor-nonnegative state.

## Dumbassery / circularity check

A proposed proof of domination must be rejected if it simply repackages any of the following:

- “the successor should be nonnegative”;
- the absence of the negative root it is supposed to prove;
- a positive-definite predecessor assumption not supplied by first-bad minimality;
- a hidden inverse at zero;
- termwise positivity of indefinite source atoms;
- generic Hermitian/parity/KKT structure already realized by countermodels;
- a scalar-shift-invariant argument that cannot locate the canonical spectral origin.

The proof earns information only if it identifies a canonical arithmetic mechanism not shared by the generic fixtures.

## Falsification gates

- test both parities;
- test the exact canonical normalization, not legacy `finiteMatrix`;
- test the shell sign and determinant separately;
- test kernel directions, where `Δ=-|b|^2` and nonnegativity demands exact coupling annihilation;
- exploit homogeneity in `w` when reducing numerical/symbolic searches;
- preserve the exact first-bad/predecessor hypotheses when claiming relevance;
- no finite-prefix or high-precision observation is theorem authority.

## Permanent claim boundary

**PROVED:** theorem authority is through PR #137, including #136 absolute energy and #137 source pairing, determinant reduction, conditional domination sufficiency, and global domination-failure/sign-witness wrappers.

**DERIVED:** domination is the one-dimensional-shell block-positivity condition under predecessor nonnegativity; a positive Gram representation of the full canonical source pairing would be a natural route to the determinant inequality if it exists.

**LEAD / HYPOTHESIS:** canonical shell-energy nonnegativity, determinant nonnegativity, Gram/integral representation, high-order cancellation as a determinant bound, A4R regular-aperture simplification.

**EXPERIMENTAL SIGNAL:** generic exact rational countermodels and any future canonical low-dimensional sign probes.

**OPEN:** canonical one-step domination, finite first-bad exclusion, unconditional negative-root exclusion, terminal Mathlib RH bridge, RH.

**RH remains OPEN.**

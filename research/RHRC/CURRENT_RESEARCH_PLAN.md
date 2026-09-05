# RHRC current research plan

> **Claim firewall: RH remains OPEN.**

## Current theorem-state anchor

~~~text
theorem-state anchor = PR #115 merge a2fecffbef8fed1fdfba373aa5756acf2618e2a1
theorem tree = 47a2601e3464b0b4248e61c52b4560681f73c986
theorem-bearing merged through = PR #115
FIRST-BAD-RIGIDITY-E1 cubic-shell incidence = PROVED / MERGED
CCM and ExceptionalZero import closure = PR #115 theorem surface
RH = OPEN
~~~

Live GitHub head + Lean/CI remain authoritative over this prose anchor.

## One-screen frontier

~~~text
DONE
  W0/W1/W2-ZS + finite legal approximation
  F1 canonical finite negative obstruction
  constrained algebra / Hermitianity / Euclidean sector
  exact centered N-flow + fixed-L negative tail
  exact reversal symmetry + even commutator collapse
  direct parity decomposition + algebraic D-equivalence
  least parity bad + predecessor nonnegative + 1D successor shell
  negative first-bad eigenmode and noninheritance
  exact parity normals + KKT
  rank-at-most-one cubic parity defect
  global first bad + intrinsic W/S block
  exact cubic factorization
  canonical V=W⊕S coordinates
  safe shifted predecessor resolvent
  basis-free scalar shifted Schur identity
  E1: canonical cubic shell coordinate != 0 in either parity / PR #115

NOW — E1b / E2: CUBIC-NORMALIZED SCHUR
  dim_C S=1 + nonzero negative-mode shell coordinate + nonzero cubic shell coordinate
    -> identify the two shell vectors up to a nonzero scalar
  transfer the #113 shifted Schur identity to the canonical cubic shell line
  normalize shell scale
  obtain a scale-free one-dimensional cubic-normalized secular equation

THEN — E3
  prove projected predecessor block A symmetric
  prove quantitative shifted coercivity for A-lam I
  derive resolvent norm/positivity consequences if Lean-cheap
  establish scalar resolvent monotonicity if possible

THEN — E4
  theoremize parity nullity-difference <=1 algebraically
  package common even/odd resonance vs one-channel opposite-parity resolvent
  classify/exclude simultaneous first-bad resonance

PARALLEL PAPER/DIAGNOSTIC LANE — DEFORMATION BUDGET
  define spectral-floor / shell-stiffness / coupling quantities without granting theorem status
  derive certified one-step deformation upper bounds only from explicit lower/upper input bounds
  require an actual infinite-tail majorant before any tail-pruning claim
  use FFBBP v1.6 decision-commutation + horizon assurance
  use RACR-style routing + MCM first-break tests
  use retroactive archaeology before promoting a new branch
  no Lean implementation until the paper/numerical route survives its first-break tests

OPTIONAL / CHEAP IF AVAILABLE
  negative index exactly one / unique negative eigenline

PARALLEL SOURCE
  G1-B1B -> G1-final -> S-NEG -> G23

RH OPEN
~~~

## What PR #115 changed

E1 is no longer a lead. The repository now proves the smaller theorem actually needed downstream: the canonical cubic parity-defect direction is not inherited from the centered predecessor and therefore has nonzero canonical intrinsic shell coordinate. The explicit closed-form projection coefficient

~~~text
alpha_K = (3 K^2 + 3 K - 1)/5
~~~

was intentionally not made a dependency and remains optional unless a later theorem needs it.

At the same global first-bad finite state we therefore have two nonzero vectors in the same one-dimensional shell:

~~~text
intrinsicShellPart p N v != 0
intrinsicCubicShellPart p N != 0
Module.finrank C S = 1
~~~

E2 is the direct composition target.

## Deformation-budget research lens

The new supporting Control-v2 layer tracks the paper-level idea that exact centered N-flow can be treated as a discrete deformation process. The candidate diagnostic state is

~~~text
mu_N     spectral floor
q_N      intrinsic shell stiffness
beta_N   shell/predecessor coupling
D_N      certified one-step downward-deformation upper bound
R_N      certified remaining deformation upper bound
H_N      certified headroom lower bound
~~~

A point estimate, small local residual or fitted tail is never enough to prune. The only decision-bearing form is a certified lower bound for the current positive margin together with a certified upper bound for the complete remaining deformation budget. Control v2 is diagnostic/routing infrastructure only; Lean remains theorem authority.

## Control-v2 integration

`research/RHRC/control_v2/` adds deterministic research routing, first-break declarations and retroactive research memory. `research/RHRC/ffbbp/v16_*` adds the newer assurance contracts without modifying or inheriting qualification from the frozen RUN42C implementation.

Every serious new branch should carry a retro-search receipt. Dead routes may not be silently resurrected. Counterfactual replay is `as_of` bounded and external historical sources require availability metadata to prevent hindsight leakage.

## E2 falsification gates

- keep predecessor size N and successor size N+1 explicit;
- use only theorem-backed 1D-shell geometry from #112/#113/#115;
- do not infer pure-shell behavior from a nonzero shell coordinate;
- do not infer shell invariance;
- D remains algebraic, not unitary/isometric;
- the scalar Schur equation can have negative roots in generic Hermitian systems;
- normalization must remove only scalar choice, not mathematical content;
- simultaneous parity resonance remains open until theoremized/excluded;
- do not introduce an RH-equivalent arithmetic estimate as an auxiliary hypothesis.

## Current claim boundary

**PROVED:** through PR #115, including intrinsic direct-sum geometry, exact cubic factorization, shifted Schur reduction and nonzero canonical cubic shell incidence at the same global first-bad state forced by an off-line zero.

**DERIVED / OPEN FORMALIZATION:** projected A symmetry, quantitative shifted coercivity, negative index exactly one, resolvent monotonicity, parity nullity difference, resonance/resolvent dichotomy.

**LEAD / HYPOTHESIS:** cubic-normalized Schur rigidity, deformation-budget asymptotics/tail certification and exclusion of the remaining first-bad state.

**OPEN:** positivity / finite-to-infinite closure / RH.

**RH remains OPEN.**

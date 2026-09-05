# RHRC current research plan

> **Claim firewall: RH remains OPEN.**

## Current authority split

~~~text
theorem-state anchor = PR #115 merge a2fecffbef8fed1fdfba373aa5756acf2618e2a1
theorem tree = 47a2601e3464b0b4248e61c52b4560681f73c986
theorem-bearing merged through = PR #115
FIRST-BAD-RIGIDITY-E1 cubic-shell incidence = PROVED / MERGED

control-plane anchor = PR #116 merge 8921572170e89d74216f0c5577b669696626219e
control-plane tree = fc138b517c6835230515167386eafe3ef3495baf
Control v2 / FFBBP v1.6 assurance = MERGED GREEN CONTROL INFRASTRUCTURE

RH = OPEN
~~~

Live GitHub head + Lean/CI remain authoritative over these prose anchors. PR #116 changed no Lean theorem authority.

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
  prefer scale-free ratios built directly from c_N = intrinsicCubicShellPart p N
  obtain a scale-free one-dimensional cubic-normalized secular equation

THEN — E3: PROJECTED SYMMETRY / COERCIVITY / RESOLVENT
  prove projected predecessor block A symmetric in the exact repository inner product
  prove quantitative shifted coercivity for A-lam I
  derive the safe resolvent norm/positivity estimate
  use E2 + E3 to theoremize a one-step deformation bound if the paper test survives
  establish scalar resolvent monotonicity only if it materially helps

THEN / PARALLEL — E4
  theoremize parity nullity-difference <=1 algebraically
  package common even/odd resonance vs one-channel opposite-parity resolvent
  classify/exclude simultaneous first-bad resonance

PARALLEL PAPER/DIAGNOSTIC LANE — DEFORMATION BUDGET
  use the theorem-backed cubic shell coordinate as the canonical shell direction
  probe g_N = q_N-mu_N, beta_N, and beta_N^2/g_N for both parities and multiple fixed L
  kill the route cheaply if the gap closes, coupling does not decay, or the ratio is not summable
  require a complete certified infinite-tail majorant before any PRUNE
  require decision commutation for reduced-model decision-bearing use
  treat the desired L condition as all-L certification / controlled L-dependence; one universal Nstar is not assumed

CONTROL HARDENING
  numeric tail != horizon certificate
  prefix steps must cover every N exactly once in sorted contiguous order
  archaeology receipts bind the exact declared search paths
  generic aliases do not count as admission-quality historical evidence
  routing remains deterministic and exposes score formula + candidate base scores
  theorem anchor and control-plane anchor stay separate

OPTIONAL / CHEAP IF AVAILABLE
  shell-projected cubic-defect zero iff cubicDefectFunctional zero
  negative index exactly one / unique negative eigenline

PARALLEL SOURCE
  G1-B1B -> G1-final -> S-NEG -> G23

RH OPEN
~~~

## What PR #115 changed

E1 is no longer a lead. The repository proves the smaller theorem actually needed downstream: the canonical cubic parity-defect direction is not inherited from the centered predecessor and therefore has nonzero canonical intrinsic shell coordinate. The explicit closed-form projection coefficient

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

## Post-#116 composition

PR #116 added no mathematical theorem, but its first real-history control run selected the deformation-budget paper test as the highest deterministic score among admissible actions and chose the shell-gap failure `q_N-mu_N` as the cheapest decisive first break. That recommendation is diagnostic only.

The stronger mathematical synthesis is that E2/E3 and the deformation-budget idea are not independent theorem routes. The expected chain is

~~~text
#115 cubic shell incidence
  -> E2 cubic-normalized Schur
  -> E3 shifted coercivity / resolvent
  -> certified one-step deformation bound
~~~

Writing

~~~text
g_N = q_N - mu_N
d_N = mu_N - lam
~~~

the intended operator estimate is expected to imply

~~~text
d_N (g_N + d_N) <= beta_N^2
~~~

and therefore the diagnostic two-by-two displacement bound, with the safe shortcut

~~~text
d_N <= beta_N^2 / g_N
~~~

when a strictly positive `g_N` lower bound is independently certified.

This remains a LEAD / HYPOTHESIS until E2/E3 supply the exact theorem hypotheses.

## Whole-N rigidity-horizon lead

Exact centered N-flow already proves upward persistence of badness. Therefore, for fixed `(L,p)`, a fully certified positive headroom

~~~text
H_Nstar = mu_lower_Nstar - R_upper_Nstar > 0
~~~

would do more than reduce the infinite search to a finite window:

- earlier badness would have persisted to `Nstar`, contradicting the positive floor there;
- later badness would be excluded by the complete remaining deformation budget.

So a genuine horizon would exclude the entire fixed-`(L,p)` N-axis. The required global target is all-`L` coverage, potentially with `Nstar=Nstar(L,p)`; a universal L-independent horizon is stronger than logically necessary.

## Cheap projected-defect composition

PR #112 proves `F_N(z)=ell_N(z) g_N`; PR #115 proves the canonical cubic shell coordinate is nonzero. Applying `intrinsicShellPart` should therefore give the cheap formalization target

~~~text
intrinsicShellPart (F_N z) = 0  <->  cubicDefectFunctional ... z = 0.
~~~

If theoremized, this identifies the cubic defect functional with visibility of the exact parity defect in the unique new N-flow quotient direction. It still does not prove the functional is nonzero on any specific vector.

## Deformation-budget falsification gates

- `q_N-mu_N` must remain usefully positive;
- `beta_N` must exhibit useful decay;
- the actual tail quantity `beta_N^2/(q_N-mu_N)` must admit a summable certified majorant, not merely tend to zero;
- the result must survive the required L range and both parity carriers;
- a local 2x2 comparison is diagnostic only; certification must come from the operator-theoretic E3 route;
- decision-bearing reduced calculations require decision commutation;
- a finite prefix, fitted tail or small residual is never an infinite-horizon certificate.

## Control-v2 integration and hardening

`research/RHRC/control_v2/` remains research-control infrastructure only. Its hardened semantics require explicit step coverage and separate horizon evidence before a complete budget can be certified. Retro receipts state the exact Git search paths, and archaeology wording must distinguish "all refs in declared paths" from "the whole repository".

The routing score remains deliberately deterministic. Evidence completeness controls admissibility; the current router does not pretend that archaeology hit content probabilistically updates route value.

Dead routes may not be silently resurrected. DR-010 remains dead: the current exact-N-flow route is not the old fitted-small-commutator/eigenvector-convergence shortcut.

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

**CI-VERIFIED CONTROL INFRASTRUCTURE:** PR #116 Control v2 / FFBBP v1.6 assurance / real-history archaeology, with no theorem authority.

**DERIVED / OPEN FORMALIZATION:** projected A symmetry, quantitative shifted coercivity, canonical scale-free cubic shell quantities, shell-projected defect-functional equivalence, negative index exactly one, resolvent monotonicity, parity nullity difference, resonance/resolvent dichotomy.

**LEAD / HYPOTHESIS:** cubic-normalized Schur rigidity, E2+E3 one-step deformation theorem, deformation-budget asymptotics/tail certification, whole-N rigidity horizon, and exclusion of the remaining first-bad state.

**OPEN:** positivity / finite-to-infinite closure / RH.

Detailed post-green lead delta: `RESEARCH_LEADS_POST_116_DELTA.md`.

**RH remains OPEN.**

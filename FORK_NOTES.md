# Fork notes — current RHRC state

> **RH remains OPEN.**

## Authority snapshot

~~~text
live main after PR #116 = 8921572170e89d74216f0c5577b669696626219e
live main tree = fc138b517c6835230515167386eafe3ef3495baf

theorem-state anchor = PR #115 merge a2fecffbef8fed1fdfba373aa5756acf2618e2a1
theorem tree = 47a2601e3464b0b4248e61c52b4560681f73c986
theorem-bearing merged through = PR #115
FIRST-BAD-RIGIDITY-E1 cubic-shell incidence = PROVED / MERGED

control-plane anchor = PR #116 merge 8921572170e89d74216f0c5577b669696626219e
Control v2 / FFBBP v1.6 assurance = MERGED GREEN CONTROL INFRASTRUCTURE

RH = OPEN
~~~

Live GitHub head + Lean/compiler/CI remain authoritative. PR #116 changed no theorem authority.

## Recent theorem packages

~~~text
#94  F1 canonical finite negative obstruction
#96  constrained canonical algebra
#98  Euclidean constrained sector
#100 exact centered N-flow + fixed-L negative tail
#102 exact reversal symmetry + even commutator collapse
#103 exact parity geometry + algebraic D-equivalence
#105 fixed-parity bad tail + least bad size + 1D successor shell
#107 parity compression + genuine negative eigenmode + non-inheritance
#109 nonzero ambient shell projection + exact parity normals + KKT
#110 cubic parity channel + rank-at-most-one compressed parity defect
#112 global first bad + intrinsic shell + exact cubic factorization
#113 intrinsic direct sum + shifted inverse + scalar Schur identity
#115 canonical cubic shell incidence in both parity carriers
~~~

## Current frontier

~~~text
FIRST-BAD-RIGIDITY-E
  E1   cubic-shell incidence                                PROVED / #115
  E1b  identify nonzero cubic/eigenmode shell coordinates  NEXT
  E2   cubic-normalized scale-free Schur equation           NEXT
  E3   projected symmetry + shifted coercivity/resolvent    DOWNSTREAM
       -> one-step deformation theorem if paper test lives
  E4   parity nullity + resonance/resolvent dichotomy       DOWNSTREAM

PARALLEL
  deformation-budget gap/coupling/summability falsifiers
  G1-B1B -> G1-final -> S-NEG -> G23
~~~

The key theorem-backed composition is

~~~text
negative-mode intrinsic shell coordinate != 0    #113
canonical cubic intrinsic shell coordinate != 0  #115
dim_C intrinsic shell = 1                        #112
~~~

E1b/E2 should therefore work directly on the one-dimensional canonical shell line rather than rebuild ambient projection geometry.

The optional explicit odd projection coefficient `alpha_K=(3K^2+3K-1)/5` was not required for #115 and remains unpromoted unless a later quantitative theorem needs it.

## Post-#116 strategic composition

PR #116 merged the Control-v2 / FFBBP-v1.6 assurance layer green without changing theorem authority. Its first real-history route certificate selected the deformation-budget paper test and the `q_N-mu_N` gap failure as the cheapest decisive falsifier.

The mathematical composition now looks like

~~~text
#115 cubic-shell incidence
  -> E2 cubic-normalized Schur
  -> E3 coercive predecessor resolvent
  -> candidate certified one-step deformation theorem.
~~~

The diagnostic lane should test

~~~text
g_N = q_N-mu_N
beta_N
beta_N^2/g_N
~~~

for both parities and several fixed positive `L` values before attempting an analytic infinite-tail majorant.

Exact N-flow already proves upward persistence of badness. A fully certified positive rigidity horizon at fixed `(L,p)` would therefore exclude the whole N-axis: earlier badness is impossible by persistence, later badness is impossible by the complete remaining-deformation budget. This remains a LEAD / OPEN certification target.

## Control hardening

The post-#116 hardening pass keeps theorem and control anchors separate and closes several control-semantic gaps:

- finite-prefix deformation bounds are indexed typed steps with exact contiguous coverage;
- a numeric tail does not become certified without a passed FFBBP horizon certificate targeting `remaining_deformation_budget`;
- reduced-model decision-bearing `PRUNE` use requires decision commutation when declared;
- retro receipts bind their exact Git search paths and archaeology is described as all refs in declared paths;
- generic `fold`, `rupture` and `slack` aliases are removed from the deformation-budget concept after the first real-history run showed overwhelming false positives;
- deterministic routing exposes its score formula and every candidate's base score/blockers.

These controls are research-governance infrastructure only. They cannot promote a theorem or emit an RH answer.

Firewalls remain: D is algebraic rather than unitary; exact factorization does not prove the defect functional nonzero; shell nonzero does not mean pure shell; no `A^-1` at zero; no negative-index-one, resolvent-monotonicity, resonance-exclusion, positivity, finite-to-infinite or RH theorem has been promoted.

Current research detail: `research/RHRC/RESEARCH_LEADS_POST_116_DELTA.md`.

**RH remains OPEN.**

# Fork notes — current RHRC state

> **RH remains OPEN.**

## Authority snapshot

~~~text
theorem-state anchor = PR #115 merge a2fecffbef8fed1fdfba373aa5756acf2618e2a1
theorem tree = 47a2601e3464b0b4248e61c52b4560681f73c986
theorem-bearing merged through = PR #115
FIRST-BAD-RIGIDITY-E1 cubic-shell incidence = PROVED / MERGED
RH = OPEN
~~~

Live GitHub head + Lean/compiler/CI remain authoritative.

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
  E4   parity nullity + resonance/resolvent dichotomy       DOWNSTREAM

PARALLEL
  deformation-budget paper/diagnostic lane
  G1-B1B -> G1-final -> S-NEG -> G23
~~~

The key composition now has theorem-backed incidence on both sides:

~~~text
negative-mode intrinsic shell coordinate != 0    #113
canonical cubic intrinsic shell coordinate != 0  #115
dim_C intrinsic shell = 1                        #112
~~~

E1b/E2 should therefore work directly on the one-dimensional canonical shell line rather than rebuild ambient projection geometry.

The optional explicit odd projection coefficient `alpha_K=(3K^2+3K-1)/5` was not required for #115 and remains unpromoted unless a later theorem needs it.

## Control-plane upgrade in PR #116

PR #116 adds RHRC Control v2 around the theorem stack:

- additive FFBBP v1.6 assurance without changing RUN42C qualification;
- deterministic RACR-style route ranking;
- MCM first-break contracts;
- read-only PIRE-style research-regime monitoring;
- deformation-budget diagnostics with explicit tail certificates;
- exhaustive retroactive Git archaeology across historical refs;
- strict `as_of` replay and hash/availability-bound external archive ingestion;
- dead-route revival records.

The controller has no theorem or claim-promotion authority and cannot emit the terminal RH answer.

Firewalls remain: D is algebraic rather than unitary; exact factorization does not prove the defect functional nonzero; shell nonzero does not mean pure shell; no `A^-1` at zero; no negative-index-one, resolvent-monotonicity, resonance-exclusion, positivity, finite-to-infinite or RH theorem has been promoted.

Current research detail: `research/RHRC/RESEARCH_LEADS_POST_115_DELTA.md`.

**RH remains OPEN.**

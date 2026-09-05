# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **RH remains OPEN.**

This fork preserves the upstream Zeta23 theorem package while adding an opt-in RH-directed research programme under `Zeta23/CCM`, `Zeta23/ExceptionalZero` and `research/RHRC`.

## Current authority snapshot

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

Live GitHub head + Lean compiler + CI remain authoritative over prose snapshots. PR #116 changed no Lean theorem authority.

## Current RH-directed theorem ladder

~~~text
off-line zeta zero
  -> compact C² pole-neutral negative W test                       PROVED
  -> strict aperture + legal finite approximation                 PROVED
  -> canonical finite negative obstruction                        PROVED / #94
  -> constrained algebra / Hermitianity / displacement            PROVED / #96
  -> Euclidean constrained sector / exact dimensions              PROVED / #98
  -> exact centered N-flow / fixed-L negative tail                PROVED / #100
  -> exact reversal symmetry / even commutator collapse           PROVED / #102
  -> direct parity geometry / algebraic D-equivalence             PROVED / #103
  -> least bad parity size + predecessor nonnegative              PROVED / #105
  -> exact one-dimensional successor parity shell                 PROVED / #105
  -> negative first-bad eigenmode + noninheritance                PROVED / #107
  -> nonzero eigenmode shell projection + parity normals/KKT      PROVED / #109
  -> cubic parity channel + compressed defect finrank <= 1        PROVED / #110
  -> global first bad + both predecessor parities nonnegative     PROVED / #112
  -> intrinsic predecessor W + shell S, dim_C S = 1               PROVED / #112
  -> exact cubic defect factorization F_N(v)=ell_N(v) g_N         PROVED / #112
  -> canonical V = W ⊕ S coordinates                              PROVED / #113
  -> safe shifted predecessor inverse / reconstruction            PROVED / #113
  -> basis-free scalar shifted Schur identity                     PROVED / #113
  -> canonical cubic shell coordinate != 0 in either parity       PROVED / #115

NOW
  E1b/E2 cubic-normalized scale-free Schur equation

THEN
  E3 projected predecessor symmetry / shifted coercivity / resolvent
  E2+E3 one-step certified deformation theorem if paper test survives
  E4 parity nullity / common-resonance vs one-channel resolvent

PARALLEL
  deformation-budget falsification lane
  source-faithful G1-B1B -> G1-final -> S-NEG -> G23

RH                                                                 OPEN
~~~

## What PR #115 changed

PR #115 theoremized the exact E1 statement needed for composition: the canonical cubic parity-defect direction is not inherited from the centered predecessor and therefore has a nonzero canonical intrinsic shell coordinate.

At the same global first-bad finite state we now have

~~~text
intrinsicShellPart p N v != 0
intrinsicCubicShellPart p N != 0
Module.finrank C (intrinsicParitySuccShell p N) = 1
~~~

so the negative-mode shell coordinate and cubic shell coordinate are two nonzero vectors in the same one-dimensional complex shell. E1b/E2 is to identify them up to a nonzero scalar, transport the #113 shifted Schur identity onto the canonical cubic shell line and normalize only scalar choice.

The stronger optional closed-form projection coefficient

~~~text
alpha_K = (3 K^2 + 3 K - 1)/5
~~~

was intentionally not made an E1 dependency and remains a lead unless separately theoremized.

## What PR #116 changed

PR #116 added a **non-authoritative research-control layer**, not a theorem result. Its validated tree was merged unchanged to main. It added deterministic route ranking, first-break contracts, FFBBP v1.6 assurance, real-history archaeology/replay and the deformation-budget diagnostic while preserving the theorem/claim firewall.

The first real-history controller run selected the deformation-budget paper test and chose failure of `q_N-mu_N` to remain usefully positive as the cheapest decisive first break. That is a research recommendation, not theorem evidence.

The post-green synthesis is stronger than the controller ranking itself:

~~~text
#115 cubic shell incidence
  -> E2 cubic-normalized Schur
  -> E3 shifted coercivity / resolvent
  -> candidate certified one-step deformation theorem
~~~

The paper lane should therefore probe

~~~text
g_N = q_N-mu_N
beta_N
beta_N^2/g_N
~~~

for both parities and several fixed positive `L` values before any attempt at an analytic infinite-tail majorant.

Exact N-flow already proves upward persistence of badness. Consequently, a genuine positive rigidity horizon plus a complete future-deformation certificate would exclude the entire fixed-`(L,p)` N-axis, not merely reduce it to a finite search window. This remains a LEAD / OPEN certification target.

## Control-v2 hardening

Control v2 now treats a complete deformation budget as a typed assured object:

- every finite-prefix step has an exact N index and prefixes must be sorted/contiguous;
- a numeric tail is not certified without a passed FFBBP horizon certificate targeting the remaining deformation budget;
- reduced-model decision-bearing `PRUNE` use requires decision commutation when declared;
- archaeology receipts bind their declared Git search paths;
- generic aliases such as `fold`, `rupture` and `slack` are removed from admission-quality deformation-budget archaeology;
- theorem and control-plane anchors are explicit and separate;
- deterministic route certificates expose the score formula and every candidate base score/blocker.

None of these mechanisms can change theorem authority or the terminal RH answer.

## Permanent firewalls

- `V = W ⊕ S` is proved, but shell invariance under the compressed operator is not.
- nonzero shell coordinate does not imply a pure-shell eigenmode.
- D-equivalence is algebraic, not unitary or isometric.
- exact factorization through `g_N` does not prove `ell_N != 0` or exact rank one.
- `g_N != 0` does not prove the parity defect operator is nonzero.
- algebraic conjugation does not automatically preserve self-adjointness in the original inner product.
- no equal-spectrum, Hermitian interlacing or inertia transfer through D is proved.
- use `A-lam I` for `lam<0`; never assume `A^-1` at zero for the semidefinite predecessor block.
- the shifted Schur identity is a reduction, not a contradiction.
- negative index exactly one, resolvent monotonicity and simultaneous-resonance exclusion remain open/formalization targets.
- the deformation-budget asymptotics/tail certificate are a lead, not a theorem.
- a finite prefix, fitted tail, local residual or diagnostic 2x2 formula is not an infinite-horizon certificate.
- generic R002 taper-grid and Bombieri zero-height truncations remain distinct from the canonical deterministic CCM finite family except where exact specialization/bridge theorems say otherwise.
- the legacy printed `finiteMatrix` differs from the canonical source matrix by a scalar identity; absolute PSD/inertia claims must use the canonical source normalization.
- positivity, finite-to-infinite closure and RH remain OPEN unless separately theorem-backed.

## Living research records

- `research/RHRC/README.md`
- `research/RHRC/CURRENT_RESEARCH_PLAN.md`
- `research/RHRC/RESEARCH_LEADS.md`
- `research/RHRC/RESEARCH_LEADS_POST_116_DELTA.md`
- `research/RHRC/OBSTRUCTION_LEDGER.md`
- `research/RHRC/DEAD_ROUTES.md`
- `research/RHRC/control_v2/README.md`
- `research/RHRC/CLAIM_REGISTRY.json`
- `research/RHRC/R003_PROMOTED_BINDINGS.json`

Machine claim/binding promotion must not be inferred beyond the entries actually present in the registries.

**RH remains OPEN.**

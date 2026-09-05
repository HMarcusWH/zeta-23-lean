# RHRC formal audit — theorem authority through PR #115; control authority through PR #116

> **RH remains OPEN.**

## Current authority split

~~~text
live main after #116 = 8921572170e89d74216f0c5577b669696626219e
live main tree = fc138b517c6835230515167386eafe3ef3495baf

theorem-state anchor = PR #115 merge a2fecffbef8fed1fdfba373aa5756acf2618e2a1
theorem tree = 47a2601e3464b0b4248e61c52b4560681f73c986
theorem-bearing merged through = PR #115
FIRST-BAD-RIGIDITY-E1 cubic-shell incidence = PROVED / MERGED

control-plane anchor = PR #116 merge 8921572170e89d74216f0c5577b669696626219e
validated PR head = b5e09880b2996e41364b3abbcc35710399a0f262
validated synthetic merge = a4d37c0fa0ce5a1e44e321924292a2b3a7920146
validated tree = fc138b517c6835230515167386eafe3ef3495baf
RHRC #776 = SUCCESS
Permansson #549 = SUCCESS
Lean CCM build = SUCCESS
Lean ExceptionalZero build = SUCCESS
forbidden-placeholder gate = SUCCESS
R003 normalization/source audit = SUCCESS
Python RHRC + Control-v2 real-history smoke = SUCCESS
RH = OPEN
~~~

The validated PR merge tree and the merged-main tree are identical. PR #116 changed no `Zeta23/**/*.lean` theorem file and does not advance mathematical theorem authority beyond PR #115.

## PR #112 — FIRST-BAD-RIGIDITY-D1

**PROVED:**
- `AnyParityBad` and a global least-bad finite size;
- both parity sectors nonnegative at every smaller size, including the predecessor of the global first bad state;
- intrinsic predecessor subspace inside the exact successor parity carrier;
- intrinsic one-step shell of complex finrank one;
- predecessor plus intrinsic shell spans the successor carrier;
- first-bad negative eigenmode has a decomposition with nonzero intrinsic shell component;
- canonical cubic defect functional;
- exact pointwise factorization of the compressed parity defect through the explicit cubic generator;
- nonzero cubic generator for `N>=2`;
- nonzero algebraic pullback of the cubic generator through D;
- ExceptionalZero endpoint packaging global first badness, KKT, intrinsic shell and exact cubic factorization at the same finite state forced by an off-line zero.

**Not proved by #112:** the defect functional is nonzero, exact rank one, D-unitarity, shell invariance, shifted Schur closure, negative index exactly one, positivity, finite-to-infinite closure or RH.

## PR #113 — FIRST-BAD-RIGIDITY-D2

**PROVED:**
- intrinsic predecessor and successor shell are complementary;
- canonical intrinsic direct-sum coordinates `W × S ≃ V`;
- canonical `intrinsicPredecessorPart` and `intrinsicShellPart`;
- exact reconstruction;
- `intrinsicShellPart_eq_zero_iff`: shell coordinate vanishes exactly on W;
- predecessor/shell orthogonality;
- first-bad negative eigenmode has nonzero canonical shell coordinate;
- projected predecessor block `A=P_W T|_W` and shell coupling `B=P_W T|_S` without W/S invariance assumptions;
- predecessor nonnegativity descends to A's self-inner form;
- for real `lam<0`, `A-lam I` is bijective;
- safe shifted predecessor equivalence/resolvent;
- first-bad block equation `(A-lam I)w=-Bs`;
- exact predecessor reconstruction `w=-(A-lam I)^(-1)Bs`;
- basis-free scalar shifted Schur identity;
- ExceptionalZero endpoint putting global first badness, both predecessor parities nonnegative, negative eigenpair, intrinsic shell, KKT, exact cubic factorization and shifted Schur reduction at one common finite problem.

## PR #115 — FIRST-BAD-RIGIDITY-E1

**PROVED:**
- every vector inherited from the centered intrinsic predecessor has zero coordinate on the new outer index;
- the odd cubic compression vector has a nonzero new outer coordinate in the stated nontrivial range;
- the odd cubic generator is not a centered predecessor extension;
- Euclidean D/N-flow compatibility needed for the algebraic even pullback;
- the corresponding even successor cubic vector is also not inherited;
- parity-uniform `successorParityCubicVector` / canonical `intrinsicCubicShellPart`;
- main E1 endpoint `intrinsicCubicShellPart p N != 0` for every parity and the stated `N>=1` range;
- ExceptionalZero endpoint adding that nonzero cubic shell coordinate to the same global-first-bad finite state already carrying #113's negative-mode shell coordinate and shifted Schur identity.

**Deliberately not proved by #115:**
- the optional closed form `alpha_K = (3K^2+3K-1)/5`;
- cubic vector is pure shell;
- shell invariance;
- D is unitary/isometric;
- `cubicDefectFunctional != 0`;
- exact defect rank one;
- cubic-normalized Schur rigidity;
- resolvent monotonicity;
- simultaneous parity-resonance exclusion;
- positivity, finite-to-infinite closure, or RH.

## PR #116 — Control v2 / FFBBP v1.6 assurance

**CI-VERIFIED CONTROL INFRASTRUCTURE:**
- Control-v2 authority firewall remains non-theorem and non-terminal;
- deterministic route ranking and first-break selection run against real repository history;
- FFBBP v1.6 assurance remains additive and does not inherit RUN42C qualification;
- diagnostic commutation, decision commutation and horizon certification stay distinct;
- counterfactual replay rejects future Git/source information;
- external archive ingestion is hash/availability bound;
- dead-route revival requires an explicit changed-premise record;
- CCM, ExceptionalZero, normalization/source firewalls and forbidden-placeholder checks remained green on the exact #116 validation tree.

**Observed post-green controller result:** the deformation-budget paper test ranked first under the configured deterministic score, and its cheapest first-break was failure of `q_N-mu_N` to remain usefully positive. This is a route recommendation, not theorem evidence.

**Observed hardening signal:** the initial deformation-budget archaeology produced overwhelming generic `fold` matches. The hardened alias surface removes generic standalone `fold`/`rupture`/`slack`, binds search paths into receipts, and states archaeology scope as all refs in declared paths.

## Current formal state

~~~text
least bad parity + predecessor nonnegative + 1D ambient shell        PROVED / #105
parity-constrained compression + negative eigenmode                  PROVED / #107
nonzero ambient successor-shell projection + exact KKT               PROVED / #109
algebraic D-equivalence + cubic defect range/finrank <=1             PROVED / #110
global first bad + both predecessor parities nonnegative             PROVED / #112
intrinsic predecessor W + intrinsic shell S, dim_C S=1               PROVED / #112
exact cubic factorization F_N(v)=ell_N(v) g_N                        PROVED / #112
canonical direct sum V=W⊕S                                            PROVED / #113
negative mode canonical shell coordinate !=0                         PROVED / #113
A-lam I bijective for lam<0                                          PROVED / #113
shifted predecessor reconstruction                                   PROVED / #113
scalar shifted Schur identity                                        PROVED / #113
canonical cubic shell coordinate !=0                                 PROVED / #115
off-line zero -> same global-first-bad Schur+cubic+E1 endpoint       PROVED / #115

Control v2 / FFBBP v1.6 assurance                                   CI-VERIFIED CONTROL / #116
cubic-normalized scale-free Schur equation                           DERIVED INTERFACE / OPEN FORMALIZATION
projected predecessor block symmetric                                DERIVED / OPEN FORMALIZATION
E2+E3 one-step deformation theorem                                   LEAD / OPEN FORMALIZATION
shell-projected defect functional equivalence                        DERIVED / OPEN FORMALIZATION
negative index exactly one / unique negative line                    DERIVED / OPEN FORMALIZATION
shifted resolvent positivity / monotonicity                           DERIVED / OPEN FORMALIZATION
parity nullity-difference <=1                                        DERIVED / OPEN FORMALIZATION
common-resonance vs one-channel-resolvent dichotomy                  DERIVED / OPEN FORMALIZATION
simultaneous parity-resonance exclusion/classification               OPEN
deformation-budget asymptotics / infinite-tail certificate           LEAD / HYPOTHESIS
whole-N rigidity horizon                                              LEAD / HYPOTHESIS
positivity / finite-to-infinite closure                              OPEN
RH                                                                    OPEN
~~~

## Current research frontier

The next theorem target remains E1b/E2. #113 and #115 give two independently constructed nonzero vectors in the same one-dimensional intrinsic shell. The immediate composition target is to identify them up to a nonzero scalar, transfer the shifted Schur identity to the canonical cubic shell line, and normalize away only scalar choice.

E3 then targets projected symmetry, quantitative shifted coercivity and the safe resolvent estimate. If the paper test survives, E2+E3 should supply the theorem mechanism for the certified one-step deformation inequality.

## Post-#116 deformation-budget strategy

Use the theorem-backed cubic shell coordinate to define scale-free `q_N` and `beta_N` candidates, then probe

~~~text
g_N = q_N-mu_N
beta_N
beta_N^2/g_N
~~~

before investing in an analytic infinite-tail majorant.

Exact N-flow already proves upward persistence of badness. Therefore a fully certified positive rigidity horizon for fixed `(L,p)` would exclude earlier badness by persistence and later badness by the complete remaining-deformation bound. The strong target is elimination of the entire fixed-`(L,p)` N-axis. All-`L` certification is eventually required, but one universal L-independent horizon is not assumed.

## Permanent firewalls

- `V=W⊕S` is proved; shell invariance is not.
- nonzero shell coordinate does not imply the vector is pure shell.
- D is algebraic, not unitary or isometric.
- exact cubic factorization does not prove the scalar functional nonzero or the defect rank exactly one.
- algebraic conjugation does not automatically preserve self-adjointness in the original even-sector metric.
- equal spectra, Hermitian interlacing and inertia transport through D are not proved.
- use `A-lam I` for `lam<0`; never replace it by `A^-1` at zero without a separate theorem.
- negative-index-one remains derived, not theorem-locked.
- the shifted Schur identity by itself is not a contradiction.
- the 2x2 deformation formula is diagnostic until E2/E3 theoremize the operator bound.
- a numeric tail, finite prefix, fitted decay or local residual is not a complete horizon certificate.
- Control-v2 diagnostics, retroactive clues and route recommendations are not theorem evidence.
- no positivity theorem, finite-to-infinite theorem or RH theorem exists.

Detailed current research implications and falsification plan: `research/RHRC/RESEARCH_LEADS_POST_116_DELTA.md`.

**RH remains OPEN.**

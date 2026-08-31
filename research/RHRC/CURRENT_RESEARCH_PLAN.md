# RHRC current research plan

> **Claim firewall: RH remains OPEN.**
>
> This is the living execution plan. It does not define theorem truth; Lean/compiler/CI plus the machine registries do that. This document answers what the project should do next, in what order, and why.

Current baseline:

~~~text
main = 09d55e93ddcb6f6765b32505309f177c9024f0cd
tree = abfce5a33d2f2562ee1e0a4b292b2cd356be5033
date = 2026-09-01
merged through = PR #75
RH = OPEN
~~~

Current theorem frontier:

~~~text
G1-B1A finite kappa/source-sector bridge = CLOSED / REGISTERED
G1-B1B Haar/L2/PsiSharp/QW bridge         = OPEN
W2 direct W/literatureRHS bridge          = OPEN
F1 canonical finite obstruction           = OPEN
~~~

The complete option inventory and historical status of individual ideas lives in RESEARCH_LEADS.md.

## 1. Plan delta after PR #75

The v1.7 handover placed W0-CONTRACTION before W2-A/B/C in the semantic build order.

The post-green review of merged #75 exposed a better execution order:

- the proof of Zeta23.EF.prop_EF_of_lit already contains almost all of W2-A internally;
- W2-A can expose a clean Summable certificate for Z.Wsummand;
- that summability package is useful for making W0-CONTRACTION legal rather than relying on unsafe tsum algebra;
- W2-B/C may collapse the shortest path to F1 onto the already-proved additive finite restriction, potentially bypassing the heavy ambient QW/form-core source chain.

Therefore the **current implementation priority** is W2-A first.

This is an execution-order optimization, not a change in logical meaning. The detector-to-obstruction semantic chain still begins with the canonical two-translate detector.

## 2. Current high-level architecture

There are now two legitimate routes from a hypothetical off-line zero to the same canonical finite obstruction.

### Internal additive route

~~~text
off-line zero
  -> canonical countable detector negative determinant          [PROVED]
  -> one negative compact C2 Weil test                          [W0 OPEN]
  -> support recentering                                        [W1 OPEN]
  -> W = literatureRHS(weilTest)                                [W2-A OPEN]
  -> literatureRHS reflection/evenization                       [W2-B OPEN]
  -> W(h,h) = localizedWeilAdditiveRHS(h,h)                     [W2-C OPEN]
  -> finite additive approximation / continuity                 [F0-B OPEN]
  -> localizedWeilAdditiveRHS(v_N,v_N)
       = quadraticForm(canonicalSourceMatrix)                    [G1-A PROVED]
  -> F1 canonical finite negative obstruction                   [OPEN]
~~~

### Source-faithful route

~~~text
off-line zero
  -> one negative compact test                                  [W0/W1]
  -> kappa/source finite sector                                 [G1-B1A PROVED]
  -> d*u / L2 / PsiSharp / QW correspondence                    [G1-B1B OPEN]
  -> QW_lambda|E_N = canonicalSourceMatrix                       [G1-final OPEN]
  -> source core / minimum-eigenvalue negative transfer         [G23 OPEN]
  -> F1 canonical finite negative obstruction                   [OPEN]
~~~

The two routes are independent enough that both are valuable. The project should choose the primary path by theorem size and hypothesis cleanliness, not sunk cost.

## 3. Exact execution queue

Semantic package IDs are authoritative. Do not reserve future PR numbers.

### P0 — W2-A direct W/literatureRHS extraction

**Priority:** IMMEDIATE  
**Information gain:** very high  
**Expected implementation risk:** low

Suggested file:

~~~text
Zeta23/ExceptionalZero/WeilLiteratureBridge.lean
~~~

Possible theorem shape:

~~~text
theorem W_eq_literatureRHS_weilTest_of_lit
    (Z : ZeroConfig)
    (hEF : EF.EF_lit Z)
    {f g : R -> C}
    (hf : ContDiff R 2 f)
    (hg : ContDiff R 2 g)
    (hfc : HasCompactSupport f)
    (hgc : HasCompactSupport g) :
    Summable (fun rho : Z.carrier => Z.Wsummand f g rho)
      /\
    Z.W f g = EF.literatureRHS (EF.weilTest f g)
~~~

Exact theorem name may change; semantic content must not.

#### Reuse rather than reprove

Extract from the existing prop_EF_of_lit proof:

- weilTest_contDiff;
- weilTest_hasCompactSupport;
- paperFT_weilTest;
- EF_lit zero-side summability;
- termwise equality between the literature zero summand and Wsummand.

#### Green gate

- exact theorem compiles;
- no unnecessary L / nuX / hFk / hmu assumptions survive;
- #print axioms remains at the intended project trust boundary;
- ClaimBindings/registry promotion only if this becomes a claim-bearing theorem.

#### Dumbassery checks

- no divergent tsum linearity;
- no accidental use of EF_paper instead of EF_lit;
- no hidden real/even restriction;
- exact conjugation argument in Wsummand preserved.

---

### P1 — W2-B literatureRHS reflection/evenization

**Priority:** NEXT IF P0 GREEN

Suggested location:

~~~text
Zeta23/ExceptionalZero/WeilLiteratureBridge.lean
~~~

or a small dedicated reflection module if the proof becomes substantial.

Targets:

~~~text
literatureRHS (fun y => k (-y)) = literatureRHS k
~~~

and the half-evenization corollary.

#### Proof obligations

- pole terms swap;
- prime term is invariant under +/- log n;
- gammaBracket reflection/evenness is theorem-locked;
- real-line gamma integral reflection is legal.

#### Green gate

No prose-only "gamma is even" step remains.

---

### P2 — W2-C diagonal W/additive bridge

**Priority:** DIRECTLY AFTER P1

Suggested file:

~~~text
Zeta23/CCM/WeilAdditiveSelfBridge.lean
~~~

Target:

~~~text
zetaZeroConfig.W f f
  = localizedWeilAdditiveRHS f f
~~~

on the exact admissible C2 compact-support class.

#### Composition

Use:

- P0 W2-A;
- P1 W2-B;
- definition of localizedWeilHalfTest as half the symmetrized correlation;
- exact argument/order conventions already theoremized in LocalizedFiniteSpace.

#### Green gate

This theorem must compare the existing genuine W with the existing additive functional. Do not define a new functional to make the statement true.

#### Strategic decision after green

Immediately reassess whether G1-B1B/G23 remain necessary for the shortest F1 route.

---

### P3 — W0-CONTRACTION: one negative function-level Weil test

**Priority:** AFTER P0-P2 unless a proof-engineering reason justifies swapping P2/P3

Suggested file:

~~~text
Zeta23/ExceptionalZero/TwoTranslateContraction.lean
~~~

Inputs:

- exists_canonicalRadiusSequence_negativeDeterminant_of_offLine_zero;
- exact two-translate phase witness;
- W hermitian/sesquilinear algebra;
- P0 summability package.

Target endpoint:

~~~text
off-line zero
  -> exists h : R -> C,
       ContDiff R 2 h
       and HasCompactSupport h
       and Re (zetaZeroConfig.W h h) < 0.
~~~

Coefficient firewall:

~~~text
z=(|C|,-C)
h=|C| k - conj(C) T_t k.
~~~

#### Green gate

- all finite W expansions summability-safe;
- exact negative real value follows from the already-proved 2x2 witness;
- no new positivity or RH statement.

#### Smoke tests

- z=(1,0);
- z=(0,1);
- C=0;
- t=0;
- C real positive;
- C real negative.

---

### P4 — W0-SMOOTH + W1 support/recentering

**Priority:** SUPPORT PACKAGE BEFORE F0

Possible files:

~~~text
Zeta23/ExceptionalZero/CanonicalNegativeTest.lean
Zeta23/ExceptionalZero/TwoTranslateSupport.lean
~~~

Tasks:

1. promote only the exact stronger detector regularity needed downstream;
2. theoremize support of the contracted test;
3. choose a finite L with strict interior margin;
4. use W_translateRight_both to recenter support inside (0,L).

#### Green gate

The resulting negative h has the exact domain/regularity hypotheses consumed by both candidate F0 routes.

---

### P5 — bounded F0-B feasibility spike

**Priority:** HIGHEST INFORMATION-GAIN FORK DECISION

Do not overbuild before determining which internal approximation route is genuinely cheaper.

#### F0-B2 first: direct additive continuity

Try to prove enough continuity for legal localized finite vectors v_N:

~~~text
localizedWeilAdditiveRHS(v_N,v_N)
  -> localizedWeilAdditiveRHS(h,h)
  = W(h,h).
~~~

Study channel by channel:

- pole evaluations;
- prime sum;
- archimedean gamma integral;
- Fourier/autocorrelation convergence.

Reuse Route-M convergence patterns where exact hypotheses align.

#### F0-B1 fallback: boundary-flat finite Fourier approximation

Construct centered finite trigonometric approximants with endpoint constraints

~~~text
sum u_n = 0
sum n u_n = 0
sum n^2 u_n = 0.
~~~

Use a fixed three-mode correction block and prove convergence in a W-controlling topology.

#### Stop rule

If the internal continuity theorem becomes a full weighted Sobolev/form-core theory larger than the exact source theorem, stop and move primary effort to P6/P8.

#### Output

The spike may legitimately end with:

- INTERNAL_ROUTE_CHEAPER;
- SOURCE_ROUTE_CHEAPER;
- BOTH_VIABLE;
- INTERNAL_BLOCKED_EXACT_REASON.

A negative feasibility result is useful research output.

---

## 4. Parallel source lane

The source lane should progress independently enough that the project is not single-threaded on F0-B.

### P6 — G1-B1B source Hilbert/functional bridge

Suggested files:

~~~text
Zeta23/CCM/SourceQWBridge.lean
Zeta23/CCM/SourceMeasure.lean
~~~

Exact subgates:

#### B1B-1 measure

Theorem-lock d*u=du/u on the exact source interval/normalization.

#### B1B-2 L2 isometry

Prove kappa preserves the exact source/additive L2 norm.

#### B1B-3 source q / PsiSharp

Formalize:

~~~text
F(u) = q(f,g)(log u)
~~~

and the exact PsiSharp functional.

#### B1B-4 QW pullback

Prove:

~~~text
QW(kappa f,kappa g) = PsiSharp(F)
~~~

on the source-valid class.

#### B1B-5 finite specialization

Only after the ambient identity is independent, specialize to the existing SourceKappa finite Fourier sector.

#### T21 gate

Before implementation, freeze:

- lambda/L convention;
- source interval;
- measure;
- kappa direction;
- q argument order;
- PsiSharp normalization;
- factor two;
- regularity class;
- exact target equality.

---

### P7 — G1-final actual finite source restriction

Target:

~~~text
QW_lambda on SourceKappa E_N
  = quadraticForm(canonicalSourceMatrix (2*log lambda) N).
~~~

Inputs:

- G1-A;
- canonical normalization repair;
- G1-B1A;
- P6.

#### Green gate

Independently defined ambient and finite objects are compared. No theorem by construction.

---

### P8 — G23 minimum source core / negative transfer, only if needed

Preferred minimal theorem:

~~~text
strict negative QW value
  -> exists N, strict negative QW value on E_N.
~~~

If the source naturally exposes the stronger minimum convergence theorem, keep it.

#### Critical firewall

Do not use bare lower semicontinuity to transfer strict negativity to approximants.

#### T22 gate

Stress any claimed uniform norm equivalence or coercivity on high-frequency source modes before relying on it.

---

## 5. Route-selection gate before F1

After P5 and enough of P6-P8 to compare theorem size, select the primary proof of F1.

### Choose internal route when

- P2 is green;
- additive continuity is clean and local;
- no heavy weighted Sobolev/form-domain machinery appears;
- approximants live in exactly the centered spaces consumed by G1-A.

### Choose source route when

- G1-B1B maps cleanly to existing source theorems;
- G23 is available with matching domain hypotheses;
- internal continuity requires a larger bespoke theory.

### Keep both when

Both close with clean independent hypotheses. Two independent proofs of F1 are high-value validation.

---

## 6. P9 — F1 canonical finite obstruction

Suggested file:

~~~text
Zeta23/CCM/CanonicalFiniteObstruction.lean
~~~

Exact target:

~~~text
(exists rho : zetaZeroConfig.carrier, (rho : C).re != 1/2)
  -> exists L : R, 0 < L
     and exists N : Nat
     and exists u : Fin (2*N+1) -> C,
       Re (quadraticForm (canonicalSourceMatrix L N) u) < 0.
~~~

#### Required firewall

- canonicalSourceMatrix only;
- no legacy finiteMatrix sign data;
- no numerical evidence in theorem dependencies;
- no hidden ambient-QW definition;
- exact zeta zero configuration language;
- all route assumptions visible.

#### Promotion rule

When F1 is green:

1. verify exact head / theorem / axioms / CI;
2. run the full Post-Green Research Pass;
3. update claim and route registries;
4. update RESEARCH_LEADS.md and this plan;
5. write the external roadmap v2.0 only then;
6. RH remains OPEN.

---

# 7. Post-F1 finite-wall program

Do not commit to this as the primary terminal route until F1 is theorem-authoritative.

## P10 — K0 canonical parity package

Suggested file:

~~~text
Zeta23/CCM/CanonicalParity.lean
~~~

Targets:

- Hermitian/real-symmetric authority;
- reversal symmetry;
- parity invariant sectors;
- D anticommutes with reversal;
- g odd;
- 1 even;
- odd vectors have zero coefficient sum.

#### Information gain

Turns rank-two displacement into one distinguished forcing channel per parity sector.

---

## P11 — K1 aperture flow / prime births / first singularity

Suggested file:

~~~text
Zeta23/CCM/CanonicalApertureFlow.lean
~~~

Targets:

1. fixed-N continuity in L;
2. continuity through prime-power births;
3. exact canonical derivative jump;
4. positive anchor for the same N;
5. existence/definition of first singular L*.

#### E2 theorem target

Re-derive whether the prime birth derivative jump is exactly rank one in J=11^T in canonical normalization.

Never copy the legacy formula without proof.

---

## P12 — K2 kernel/displacement/parity rigidity

Suggested file:

~~~text
Zeta23/CCM/CanonicalKernelRigidity.lean
~~~

At a singular M u=0, theorem-lock:

~~~text
M(Du) = -g(1^T u) + 1(g^T u)
~~~

with exact sign/order.

Then split:

~~~text
u even -> g^T u = 0
u odd  -> 1^T u = 0.
~~~

Do not assume simple kernel.

---

## P13 — K2 resolvent composition

Only after K0/K1/K2 exactness, introduce parity-block resolvents:

~~~text
m_even(z) = <1,(M_even-z)^(-1)1>
m_odd(z)  = <g,(M_odd-z)^(-1)g>.
~~~

Promotion test: derive a real crossing/sign restriction, not a restatement of standard resolvent algebra.

---

## P14 — K3 arithmetic crossing engine

Compose only theorem-authoritative pieces:

- canonical E2 prime-event flow;
- E5 Sherman-Morrison/Weyl/spectral-measure channel;
- E7 parity-reduced barycentric equation;
- T23 crossing/degeneracy classification;
- Schur/LDL/principal-minor constraints.

Branch classification should explicitly separate:

- simple even crossing;
- simple odd crossing;
- simultaneous parity-sector singularity;
- higher-dimensional kernel.

Kill E7 immediately if it adds no information beyond M u=0.

---

## P15 — terminal structural exclusion target

Desired theorem shape:

~~~text
the first canonical zero-crossing state demanded by F1
cannot satisfy the exact arithmetic + parity + displacement + resolvent laws.
~~~

Do not replace this with a bald universal PSD assertion without acknowledging that such a theorem is likely RH-strength once the surrounding equivalences are in place.

RH remains OPEN until the exact terminal RH theorem itself passes proof and claim validation.

---

# 8. Alternate routes and when to activate them

## Suzuki

Keep as ACTIVE ALTERNATE / CROSS-CHECK.

Activate strongly if its exact fixed-aperture negative-bottom theorem can feed P7/P8 cleanly or gives an independent proof of F1.

## R002

Keep separate. Use pair-level negativity as an adversarial motif, but do not reintroduce generic taper-grid = CCM.

## Bombieri

Comparator only unless an exact change-of-basis/compression/congruence/inertia-transfer theorem appears.

## Connes / finite Xi

Dormant longer route. Resume if F1/finite-wall stalls or a local-uniform determinant-to-Xi convergence theorem becomes available.

## R004 analytic generator

Dormant-but-valid. Revival requires explicit generator + absolute commutator + non-collapsing gap theorem.

---

# 9. Numerical / experimental work allowed now

Numerical work should maximize theorem information, not merely produce pretty spectra.

Allowed high-value experiments:

- canonicalSourceMatrix only for sign/inertia/lower-bound work;
- first-crossing searches by fixed N;
- prime-power threshold tracking;
- parity-sector eigenvalue tracking;
- all-ones / g-channel spectral weights;
- high-frequency T22 falsifiers;
- F0-B2 additive-continuity prototypes;
- detector radius/aperture/bandwidth scaling.

Every numerical record should include:

- exact object;
- L / lambda;
- N;
- prime thresholds;
- precision;
- canonical vs legacy normalization;
- hypothesis being tested;
- explicit falsification criterion.

Experimental signal is not theoremhood.

---

# 10. Permanent stop / falsification rules

Stop a branch immediately when:

- it requires a known RH-equivalent target as an "auxiliary estimate";
- it silently identifies legacy finiteMatrix with canonical source/QW;
- it reuses generic R002 taper-grid = CCM;
- it assumes Bombieri and CCM finite truncations are the same object;
- it expands ZeroConfig.W by finite linearity without summability;
- it treats global C2 zero extension of arbitrary localizedFiniteVector as automatic;
- it uses lower semicontinuity alone to move strict negativity to approximants;
- it relies on uniform high-frequency coercivity that T22 falsifies;
- a proposed barycentric/resolvent identity is algebraically equivalent to M u=0 and adds no new constraint;
- a fitted generator has collapsing gaps and no independent analytic gap theorem.

A killed route should be recorded in DEAD_ROUTES.md and RESEARCH_LEADS.md with the exact changed-premise condition required for revival.

---

# 11. Documentation and post-green maintenance

After every meaningful green package:

### Formal truth update

- theorem source;
- #print axioms surface;
- ClaimBindings if promoted;
- CLAIM_REGISTRY.json;
- ROUTE_REGISTRY.json.

### Living research update

- relevant route README;
- RESEARCH_LEADS.md;
- CURRENT_RESEARCH_PLAN.md;
- root README if the public critical path changed;
- AUDIT.md if the repository audit baseline/state materially changed.

### Historical material

Do not rewrite historical settlements merely to make them current.

---

# 12. Current one-screen plan

~~~text
NOW
  P0 W2-A direct W -> literatureRHS extraction
  P1 W2-B reflection/evenization
  P2 W2-C W(h,h) -> localizedWeilAdditiveRHS

THEN
  P3 W0 contraction -> one negative W test
  P4 W0 smoothness/support/recentering
  P5 bounded F0-B2/F0-B1 feasibility spike

PARALLEL
  P6 G1-B1B Haar/L2/PsiSharp/QW
  P7 G1-final actual source restriction
  P8 G23 minimum negative-transfer theorem if needed

DECISION
  choose internal route / source route / both

TARGET
  P9 F1:
  off-line zero -> negative canonical finite quadratic form

POST-F1
  P10 K0 parity
  P11 K1 first singularity + canonical prime events
  P12/P13 K2 kernel/displacement/resolvent rigidity
  P14 K3 arithmetic crossing engine
  P15 structural exclusion

TERMINAL
  exact RH theorem only
~~~

## Standing priority question

At every green state ask:

> Which next theorem most reduces the admissible counterexample space per unit of new hypothesis and proof machinery?

That question, not historical PR numbering, controls this plan.

RH remains **OPEN**.

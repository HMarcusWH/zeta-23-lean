# RHRC current research plan

> **Claim firewall: RH remains OPEN.**
>
> This is the living execution plan. It does not define theorem truth; Lean/compiler/CI plus the machine registries do that. This document answers what the project should do next, in what order, and why.

Current merged validation baseline:

~~~text
main = 3e39ce86d27a4c642a1e0364f1954968ce22f1f4
tree = 6935902fbbb950847e1cdd16a61d95704e3a760d
merged through = PR #79
W0 theorem-green head = c8112f0ad12e0b2c2f1261cea3ba7726aa04be54
date = 2026-09-01
RH = OPEN
~~~

PR #79 merged the exact W0 theorem tree that passed the CCM build, ExceptionalZero build, no-placeholder gate, RHRC regression suite, normalization/source firewalls, and independent verification workflow.

Current theorem frontier:

~~~text
W2-A genuine W/literatureRHS + pairwise summability = CLOSED / REGISTERED
W0 off-line zero -> compact C² pole-neutral negative W test = CLOSED / REGISTERED
W1 strict finite-aperture support/recentering = OPEN / IMMEDIATE

INTERNAL AFTER W1
  W2-B reflection/evenization                 = OPEN
  W2-C genuine W self -> localized additive   = OPEN
  F0-B finite approximation                   = OPEN
  G1-A finite additive restriction            = CLOSED / REGISTERED

SOURCE AFTER W1
  G1-B1B Haar/L²/PsiSharp/QW                  = OPEN
  G1-final actual source restriction          = OPEN
  G23 negative finite transfer                = OPEN

F1 canonical finite obstruction               = OPEN
RH                                             = OPEN
~~~

The complete option inventory and historical status of individual ideas lives in RESEARCH_LEADS.md.

## 1. Plan delta after green W0 / PR #79

W0 closed with a stronger and cleaner endpoint than the pre-implementation roadmap expected.

Lean now proves, for every concrete off-line zeta zero `rho0`,

~~~text
(rho0 : C).re != 1/2
  ->
exists h : R -> C,
  ContDiff R 2 h
  and HasCompactSupport h
  and paperFT h ( I/2) = 0
  and paperFT h (-I/2) = 0
  and Re (zetaZeroConfig.W h h) < 0.
~~~

The physical contraction is theorem-authoritatively

~~~text
h = ‖C‖ * k - conj(C) * translateRight k t,
C = weilRelativeCorrelation zetaZeroConfig k t,
~~~

with the coefficient orientation forced by the repository convention that `W` is linear in its first slot and conjugate-linear in its second.

### What changed versus the old W0 plan

The proof did **not** need the X4.6 canonical negative-determinant endpoint or a determinant-gap converse. It used the already-proved X3 strict correlation-over-diagonal witness directly.

The proof also did **not** need new translation regularity lemmas; `contDiff_translateRight` and `hasCompactSupport_translateRight` already existed.

The load-bearing new work was:

- exact Fourier linearity for the physical two-translate combination;
- four W2-A pairwise summability certificates;
- pointwise Wsummand expansion;
- legal `tsum` recombination;
- exact equality with the existing 2x2 matrix quadratic;
- preservation of the pole-killing Fourier zeros.

This compresses the dependency graph and makes W1 the unique route-general next package.

### New structural consequence

A hypothetical off-line zero now yields an **actual function-level obstruction**, not merely a negative matrix direction. The obstruction is already pole-neutral, which removes the pole terms from the later specialized explicit-formula reflection/evenization analysis.

The X4.6 canonical detector bank remains mathematically valuable for countable RH-equivalent criteria and reproducible detector architecture, but it is not required on the shortest W0 -> F1 path.

## 2. Current high-level architecture

The shared route-general front end is now:

~~~text
off-line zero
  -> W0 compact C² pole-neutral h with Re W(h,h)<0       [PROVED]
  -> W1 translate/recenter h into strict (0,L) support   [OPEN / NEXT]
~~~

After W1 the program deliberately branches.

### Internal additive route

~~~text
W1 strict finite-aperture negative test
  -> W2-A W = literatureRHS(weilTest)                    [PROVED]
  -> W2-B reflection/evenization                         [OPEN]
  -> W2-C W(h,h) = localizedWeilAdditiveRHS(h,h)         [OPEN]
  -> finite additive approximation / continuity          [F0-B OPEN]
  -> localizedWeilAdditiveRHS(v_N,v_N)
       = quadraticForm(canonicalSourceMatrix)             [G1-A PROVED]
  -> F1 canonical finite negative obstruction            [OPEN]
~~~

Because the W0 test is pole-neutral, W2-B should first be attempted on the actual pole-neutral diagonal class before proving a maximally general reflection theorem. The prime term is structurally symmetric; the remaining analytic core is the gamma-bracket reflection/change-of-variable step.

### Source-faithful route

~~~text
W1 strict finite-aperture negative test
  -> kappa/source finite sector                          [G1-B1A PROVED]
  -> d*u / L² / PsiSharp / QW correspondence            [G1-B1B OPEN]
  -> QW_lambda|E_N = canonicalSourceMatrix              [G1-final OPEN]
  -> source core / strict negative finite transfer      [G23 OPEN]
  -> F1 canonical finite negative obstruction           [OPEN]
~~~

The two routes should progress in parallel after W1. Select the primary F1 proof by theorem size, hypothesis cleanliness and information gain, not by historical ordering.

## 3. Exact execution queue

Semantic package IDs are authoritative. Do not reserve future PR numbers.

### P0 — W2-A direct W/literatureRHS extraction

**Status:** CLOSED / PROVED  
**Claim:** `R003_WEIL_PAIR_LITERATURE_BRIDGE`  
**Theorem:** `Zeta23.ExceptionalZero.zeta_W_literatureRHS_package`

Exact theorem-green head:

~~~text
509645ad2b30288d175ff2ef5a6651839991649e
~~~

What Lean established:

~~~text
f : C² + compact support
g : continuous + compact support

=> Summable (zeta Wsummand f g)
and
   W(f,g) = literatureRHS(weilTest f g).
~~~

Axiom surface:

~~~text
[propext, Classical.choice, Quot.sound]
~~~

No aperture, `nuX`, Fourier-integrability side hypotheses, reality/evenness, or source `QW` assumptions survived.

The result is stronger than the planned interface in the second leg and supplies the exact summability package needed by P3/W0.


---

### P1 — W2-B literatureRHS reflection/evenization

**Priority:** ACTIVE INTERNAL-LANE PACKAGE AFTER W0/W1

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

**Priority:** DIRECTLY AFTER P1 ON THE INTERNAL LANE

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

**Status:** CLOSED / PROVED / REGISTERED  
**Claim:** `R003_NEGATIVE_WEIL_TEST_CONTRACTION`  
**Primary theorem:** `Zeta23.ExceptionalZero.exists_poleNeutral_negativeWeilTest_of_offLine_zero`  
**Source:** `Zeta23/ExceptionalZero/TwoTranslateContraction.lean`

Exact theorem-green head:

~~~text
c8112f0ad12e0b2c2f1261cea3ba7726aa04be54
~~~

Merged via PR #79 into:

~~~text
3e39ce86d27a4c642a1e0364f1954968ce22f1f4
~~~

Axiom surface:

~~~text
[propext, Classical.choice, Quot.sound]
~~~

### Exact proved endpoint

For every concrete off-line zero:

~~~text
(rho0 : C).re != 1/2
  ->
exists h : R -> C,
  ContDiff R 2 h
  and HasCompactSupport h
  and paperFT h ( I/2) = 0
  and paperFT h (-I/2) = 0
  and Re (zetaZeroConfig.W h h) < 0.
~~~

The weaker route-composition endpoint without the pole-neutral clauses is also theorem-locked.

### Exact contraction law

For matrix coefficients `(a,b)`, the physical test is

~~~text
conj(a) * k + conj(b) * translateRight k t.
~~~

For the existing phase witness `(‖C‖,-C)`:

~~~text
h = ‖C‖ * k - conj(C) * translateRight k t.
~~~

Lean proves the genuine W self-value equals the existing two-translate matrix quadratic exactly.

### Actual proof route

The shortest proof used the X3 theorem

~~~text
exists_realEven_poleKilled_twoTranslate_negativeWitness_of_offLine_zero
~~~

directly. It did not require the X4.6 canonical determinant endpoint, a determinant-gap converse, or new translation regularity infrastructure.

W2-A was cashed out through four explicit pairwise `Summable` certificates before any finite `tsum` algebra.

### Post-green implications

- W1 is now the route-general frontier.
- Pole neutrality survives the contraction.
- The internal W2-B package can be specialized to the actual pole-neutral negative test class.
- X4.6 remains an independent canonical/countable detector criterion, not a required dependency for F1.
- No reality/evenness property is claimed for the contracted `h`.

---

### P4 — W1 support/recentering into a strict finite aperture

**Priority:** IMMEDIATE / ROUTE-GENERAL NEXT PACKAGE

Suggested file:

~~~text
Zeta23/ExceptionalZero/NegativeWeilTestSupport.lean
~~~

### Input

Consume the strong W0 endpoint:

~~~text
C² h
HasCompactSupport h
paperFT h (±I/2) = 0
Re W(h,h) < 0.
~~~

### Target

Prove a pointwise off-line-zero endpoint of the form

~~~text
(rho0 : C).re != 1/2
  ->
exists L : R, 0 < L
and exists h : R -> C,
  ContDiff R 2 h
  and tsupport h ⊆ Ioo 0 L
  and paperFT h ( I/2) = 0
  and paperFT h (-I/2) = 0
  and Re (zetaZeroConfig.W h h) < 0.
~~~

Use a strict interior interval, not merely `Icc 0 L`, so endpoint jets vanish automatically for the recentered test and both downstream routes receive the strongest clean domain object.

### Build contract

1. extract a finite two-sided bound on `tsupport h` from `HasCompactSupport h`;
2. choose a translation amount and an `L>0` with explicit positive margin;
3. theoremize the translated support inclusion under the repository's exact `translateRight k t = k(x-t)` convention;
4. use `contDiff_translateRight` and `hasCompactSupport_translateRight`;
5. use `paperFT_translateRight` to preserve both pole zeros;
6. use `W_translateRight_both` to preserve the negative W self-value.

### Dumbassery / falsification gates

- verify the sign of the support translation explicitly;
- do not infer strict interior support from compactness without choosing a positive margin;
- do not lose pole neutrality during recentering;
- do not replace `tsupport` by ordinary support silently;
- do not add stronger smoothness than C² unless a downstream theorem actually needs it.

### Green gate

One theorem-backed object simultaneously satisfies the exact finite-aperture/domain hypotheses needed to start both the internal additive and source-faithful lanes.

### Post-green route decision

After W1 green, run a bounded comparison:

~~~text
INTERNAL:
  specialized pole-neutral W2-B
  -> W2-C
  -> F0-B

SOURCE:
  G1-B1B
  -> G1-final
  -> G23.
~~~

Do not commit to one branch before measuring actual theorem surface.

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

This is the preferred **planned** post-F1 research program, not yet a theorem-backed terminal reduction. F1 must first become theorem-authoritative. K1 must then prove the positive-anchor/continuous-aperture mechanism that turns an F1 negative value into a first canonical singular crossing for the same finite sector before a terminal first-crossing contradiction is a legitimate target.

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

## P15 — planned structural exclusion target

Conditional desired theorem shape, **after K1 has theoremized the first-crossing reduction**:

~~~text
F1 negative canonical finite value
  -> same finite sector has a first canonical singular crossing L*
  -> every such first crossing obeys the K0/K1/K2/K3 laws
  -> no state can obey all of those laws
  -> contradiction.
~~~

Only after those arrows are separately theorem-authoritative may the project compose

~~~text
off-line zero -> F1 -> impossible first crossing -> no off-line zero -> RH.
~~~

Do not replace this with a bald universal PSD assertion without acknowledging that such a theorem is RH-strength once the surrounding implications are in place.

RH remains OPEN until the exact final RH theorem itself passes proof and claim validation.

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
DONE
  W2-A genuine W -> literatureRHS + summability
  W0 off-line zero -> one negative compact C² pole-neutral Weil test

NOW
  W1 support/recentering into a strict finite aperture

THEN / PARALLEL
  INTERNAL:
    W2-B reflection/evenization
    W2-C genuine W self-value -> localized additive RHS
    F0-B finite approximation
    G1-A finite additive restriction [already proved]

  SOURCE:
    G1-B1B Haar/L²/PsiSharp/QW
    G1-final actual source restriction
    G23 negative finite transfer

TARGET
  F1:
  off-line zero -> negative canonical finite quadratic form

POST-F1 — PLANNED, NOT YET A TERMINAL REDUCTION
  K0 parity
  K1 aperture flow + positive anchor + first singularity + prime-event law
  K2 kernel/displacement/resolvent rigidity
  K3 arithmetic crossing exclusion

CONDITIONAL TERMINAL COMPOSITION
  after K1 proves F1 -> first canonical crossing:
  prove every demanded first canonical crossing impossible
  -> no off-line zero
  -> RH
~~~

## Standing priority question

At every green state ask:

> Which next theorem most reduces the admissible counterexample space per unit of new hypothesis and proof machinery?

That question, not historical PR numbering, controls this plan.

RH remains **OPEN**.

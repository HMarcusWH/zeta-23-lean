# RHRC current research plan

> **Claim firewall: RH remains OPEN.**
>
> This is the living execution plan. It does not define theorem truth; Lean/compiler/CI plus the machine registries do that. This document answers what the project should do next, in what order, and why.

Current merged validation baseline:

~~~text
main = 8960b80b4a871bd86f94509dfa872ecc6939b0cd
tree = 956601c77d1e9f32bab339dbbb81130296d1b5c7
merged through = PR #80
W1 Stage-A theorem-green head = 7abdaaf88f0e157c11049a0e65ebcb2c48fa86e2
date = 2026-09-01
RH = OPEN
~~~

The W1 Stage-A theorem head passed both repository workflows: CCM build, ExceptionalZero build, no-placeholder gate, RHRC regression suite, normalization/source firewalls and independent Permansson verification. The promotion/documentation head in PR #81 must pass the same exact-head gate before merge.

Current theorem frontier:

~~~text
W2-A genuine W/literatureRHS + pairwise summability = CLOSED / REGISTERED
W0 off-line zero -> compact C² pole-neutral negative W test = CLOSED / REGISTERED
W1 strict finite-aperture support/recentering = CLOSED / PROVED ON #81 STAGE-A

NOW — BOUNDED ROUTE COMPARISON
  INTERNAL:
    I0 pole neutrality -> weilTest(h,h) pole neutrality
    I1 mu/gamma reflection/evenness
    I2 weighted gamma-channel integrability
    then W2-B/W2-C if bounded
  SOURCE:
    S0 exact L <-> lambda bridge
    S1 G1-B1B premise/normalization lock
    then G1-B1B/G1-final/G23 if bounded

G1-A finite additive restriction            = CLOSED / REGISTERED

F1 canonical finite obstruction               = OPEN
RH                                             = OPEN
~~~

The complete option inventory and historical status of individual ideas lives in RESEARCH_LEADS.md.

## 1. Plan delta after green W1 / PR #81 Stage A

W1 closed the entire route-general front end with a stronger geometric object than the roadmap minimum.

Lean now proves, for every concrete off-line zeta zero `rho0`,

~~~text
(rho0 : C).re != 1/2
  ->
exists L > 0, r > 0, h,
  L = 4*r
  and ContDiff R 2 h
  and HasCompactSupport h
  and tsupport h ⊆ Ioo r (3*r)
  and tsupport h ⊆ Ioo 0 L
  and paperFT h ( I/2) = 0
  and paperFT h (-I/2) = 0
  and Re (zetaZeroConfig.W h h) < 0.
~~~

The proof is purely geometric/transport:

~~~text
compact tsupport h
  -> bounded
  -> choose r>0 with tsupport h ⊂ (-r,r)
  -> translateRight by 2r
  -> tsupport ⊂ (r,3r)
  -> choose L=4r
  -> tsupport ⊂ (0,L).
~~~

Existing `contDiff_translateRight`, `hasCompactSupport_translateRight`,
`paperFT_translateRight` and `W_translateRight_both` preserve every load-bearing
W0 property.

### What changed

The shared front end is no longer a research bottleneck. Both the internal and source
routes now receive the same theorem-backed object with:

- finite positive aperture;
- strict boundary margin;
- C² regularity;
- compact closed support;
- both pole-killing Fourier zeros;
- strict negative genuine Weil self-value.

The explicit margin `(r,3r)` is stronger than merely `(0,L)` and may materially
simplify boundary-flat finite Fourier approximation.

### New route-selection correction

The internal lane is **not** yet known to be cheaper merely because pole neutrality
kills the pole term.

The existing explicit-formula proof makes a separate legal-analysis requirement explicit:

~~~text
Integrable (
  fun tau =>
    paperFT (EF.weilTest h h) tau * (mu tau : C)
).
~~~

Bochner `integral_add` requires integrability. Therefore W2-B/C must not repeat the
old tsum mistake at the integral level.

The bounded internal probe is now:

~~~text
I0  pole zeros of h -> pole zeros of EF.weilTest h h
I1  mu/gamma reflection evenness
I2  weighted gamma-channel integrability
~~~

Only if I1+I2 are bounded should the project commit to W2-B/W2-C as the primary lane.

In parallel the source probe should freeze the exact W1 aperture-to-source interface:

~~~text
lambda = exp(L/2)
1 < lambda
sourceLength lambda = L
d*u = du/u
L² normalization
q argument order
PsiSharp/QW normalization
factor-of-two convention.
~~~

## 2. Current high-level architecture

The shared route-general front end is now:

~~~text
off-line zero
  -> W0 compact C² pole-neutral h with Re W(h,h)<0       [PROVED]
  -> W1 strict (0,L) support with explicit margin         [PROVED]
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

Because the W1 test is pole-neutral, W2-B should first be attempted on the actual pole-neutral diagonal class. But reflection symmetry is not the only gate: legal weighted gamma/mu integrability must also be theoremized before splitting/averaging the Bochner integral. The internal route begins with I0/I1/I2 above, not with an assumed generic literatureRHS linearity theorem.

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

**Status:** CLOSED / PROVED ON EXACT STAGE-A HEAD  
**Claim:** `R003_STRICT_APERTURE_NEGATIVE_WEIL_TEST`  
**Primary theorem:** `Zeta23.ExceptionalZero.exists_strictAperture_poleNeutral_negativeWeilTest_of_offLine_zero`  
**Source:** `Zeta23/ExceptionalZero/NegativeWeilTestSupport.lean`

Exact Stage-A theorem-green head:

~~~text
7abdaaf88f0e157c11049a0e65ebcb2c48fa86e2
~~~

Axiom surface:

~~~text
[propext, Classical.choice, Quot.sound]
~~~

### Exact proved endpoint

For each concrete off-line zero:

~~~text
exists L > 0, r > 0, h,
  L = 4*r
  and ContDiff R 2 h
  and HasCompactSupport h
  and tsupport h ⊆ Ioo r (3*r)
  and tsupport h ⊆ Ioo 0 L
  and paperFT h ( I/2) = 0
  and paperFT h (-I/2) = 0
  and Re W(h,h) < 0.
~~~

### Exact geometry

~~~text
tsupport h0 ⊂ (-r,r)
translateRight h0 (2r)
  -> tsupport ⊂ (r,3r)
L = 4r.
~~~

The proof uses exact `tsupport_comp_eq_preimage` transport; it does not silently replace
closed support by ordinary support.

### Post-green implications

- W0+W1 now form a complete route-general front end.
- The explicit positive boundary margin is available to F0-B1.
- Pole neutrality survives recentering.
- W negativity is unchanged exactly by common translation.
- The next task is route comparison, not more support infrastructure.

---

### P5 — bounded post-W1 route-comparison pass

**Priority:** IMMEDIATE / HIGHEST INFORMATION GAIN

Do not commit to either route before falsifying its first hidden premise.

#### INTERNAL-I0 — pole-neutrality transfer to the Weil test

For the actual W1 object `h`, theoremize cheaply:

~~~text
paperFT h ( I/2) = 0
paperFT h (-I/2) = 0
  ->
paperFT (EF.weilTest h h) ( I/2) = 0
paperFT (EF.weilTest h h) (-I/2) = 0.
~~~

Use the already-proved `paperFT_weilTest` factorization.

#### INTERNAL-I1 — reflection weight

Prefer the existing density `mu` through `EF.gamma_term`.

Target:

~~~text
mu (-r) = mu r.
~~~

Do not reopen a duplicate gammaBracket theory unless the mu formulation is harder.

#### INTERNAL-I2 — weighted gamma-channel integrability

The load-bearing legal requirement is:

~~~text
Integrable (
  fun r =>
    paperFT (EF.weilTest h h) r * (mu r : C)
).
~~~

This is separate from evenness. It is required before legal use of `integral_add`
or reflected-average splitting.

Use the existing C² compact-support Fourier decay machinery if the theorem surface is
bounded. If proving this becomes a large special-function/weighted-Fourier project, stop.

#### INTERNAL continuation if I0-I2 are bounded

Then prove the specialized pole-neutral diagonal W2-B/W2-C bridge and only afterward
start F0-B.

F0-B2 first: direct additive continuity.

Fallback F0-B1: boundary-flat Fourier approximation. The W1 margin
`tsupport h ⊂ (r,3r) ⊂ (0,4r)` is now a theorem-backed asset for endpoint-flat
constructions.

#### SOURCE-S0 — aperture/source parameter bridge

For `L>0`, target:

~~~text
lambda := exp(L/2)
1 < lambda
sourceLength lambda = L.
~~~

Keep this in the source lane; do not contaminate W1 with source semantics.

#### SOURCE-S1 — G1-B1B premise lock

Before implementation freeze:

- source interval;
- Haar measure `d*u = du/u`;
- exact L² normalization;
- kappa direction;
- q argument order;
- PsiSharp normalization;
- QW normalization;
- factor two;
- regularity/domain class.

#### Decision rule

Choose INTERNAL when I1/I2 close locally and F0-B remains smaller than source G23.

Choose SOURCE when gamma/mu integrability or internal continuity balloons while
G1-B1B/G23 remain local.

Keep both if both are clean.

---

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
  W1 -> same negative test in strict finite aperture with explicit margin

NOW — BOUNDED ROUTE COMPARISON
  INTERNAL:
    I0 pole neutrality -> weilTest pole neutrality
    I1 mu/gamma reflection evenness
    I2 weighted gamma-channel integrability
    if bounded:
      W2-B
      W2-C
      F0-B
      G1-A [already proved]

  SOURCE:
    S0 L <-> lambda exact bridge
    S1 G1-B1B premise/normalization lock
    if bounded:
      G1-B1B Haar/L²/PsiSharp/QW
      G1-final actual source restriction
      G23 negative finite transfer

DECIDE PRIMARY ROUTE
  by exact theorem surface and information gain

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

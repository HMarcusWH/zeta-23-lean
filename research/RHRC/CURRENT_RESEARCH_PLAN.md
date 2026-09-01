# RHRC current research plan

> **Claim firewall: RH remains OPEN.**
>
> This is the living execution plan. It does not define theorem truth; Lean/compiler/CI plus the machine registries do that. This document answers what the project should do next, in what order, and why.

Current merged validation baseline:

~~~text
main = 5134e81c0ce3fa37ef593eb96125d8e4d5aa09b8
tree = ec9fe4aac0b82b4684fa549f9509ffd2bffb2cb7
merged through = PR #82
PR #82 final validated head = d272e447c5270a287488ee015dbf589f3942d68d
date = 2026-09-01
RH = OPEN
~~~

The final PR #82 head `d272e447c5270a287488ee015dbf589f3942d68d` passed the full repository validation surface: CCM build, ExceptionalZero build, no-placeholder gate, RHRC regression suite, normalization/source firewalls and independent Permansson verification. GitHub main contains it through merge commit `5134e81c...`. PR #82 changed documentation/research priority only; the theorem frontier remains W1 while W2-ZS is a lead on merged main.

Current theorem frontier:

~~~text
W2-A genuine W/literatureRHS + pairwise summability = CLOSED / REGISTERED
W0 off-line zero -> compact C² pole-neutral negative W test = CLOSED / REGISTERED
W1 strict finite-aperture support/recentering = CLOSED / MERGED / REGISTERED

NOW — W2-ZS CONCRETE-ZETA ZERO-SIDE EVENIZATION SPIKE
  ZS0 conjugation zero/multiplicity transport
  ZS1 rho |-> 1-rho carrier equivalence
  ZS2 gammaOf sign reversal
  ZS3 paperFT reflection
  ZS4 summability-safe EF_lit zero-sum reindex
  ZS5 half-evenized literatureRHS equality
  ZS6 direct W self = localizedWeilAdditiveRHS

PARALLEL SOURCE INFRASTRUCTURE
  S-GEOM exact L <-> lambda bridge
  S-IFACE G1-B1B premise/normalization lock

SOURCE SIGN ENTRY
  S-NEG independent fixed-aperture negative-QW theorem, or
  exact W/localized-additive/QW sign-carrying composition

FALLBACK INTERNAL
  I0 pole-neutrality transfer
  I1 mu/gamma reflection/evenness
  I2 weighted gamma-channel integrability

G1-A finite additive restriction = CLOSED / REGISTERED
F0-B finite approximation = OPEN
F1 canonical finite obstruction = OPEN
RH = OPEN
~~~

The complete option inventory and historical status of individual ideas lives in RESEARCH_LEADS.md.

## 1. Plan delta after merged green W1 / PR #81

W1 closed the route-general front end with a stronger geometric object than the roadmap minimum.

Lean proves, for every concrete off-line zeta zero `rho0`,

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

The proof is purely geometric/transport. Existing `contDiff_translateRight`, `hasCompactSupport_translateRight`, `paperFT_translateRight` and `W_translateRight_both` preserve every load-bearing W0 property.

### What changed

The shared front end is no longer a research bottleneck. Both internal and source routes now receive the same theorem-backed object with finite positive aperture, strict boundary margin, C² regularity, compact closed support, pole neutrality and a strict negative genuine Weil self-value.

Because `L=4r`, the W1 theorem immediately yields the **DERIVED** stronger collar

~~~text
tsupport h ⊂ (L/4, 3L/4).
~~~

Under `lambda = exp(L/2)` and `x = log(lambda*u)`, the midpoint `x=L/2` maps to `u=1` and the W1 support collar maps to the **DERIVED** multiplicative subinterval

~~~text
(lambda^(-1/2), lambda^(1/2))
~~~

inside `(lambda^-1,lambda)`. This may simplify source-domain and finite-approximation arguments, but it is not a separately formalized theorem.

### Post-green route correction: attack the zero sum before the gamma integral

The previous plan treated mu/gamma reflection and weighted gamma-channel integrability as the next internal bottleneck. The W1 post-green pass found a smaller concrete-zeta route.

The repository already contains unconditional concrete zeta Schwarz reflection and conjugation-invariance of analytic order (`riemannZeta_conj`, `analyticOrderAt_zeta_conj`), while `zetaZeroConfig` already carries the functional-equation reflection `rho -> 1-conj(rho)` with multiplicity.

Composing these symmetries suggests the concrete carrier involution

~~~text
rho -> 1-rho
~~~

with

~~~text
gammaOf(1-rho) = -gammaOf(rho).
~~~

If theoremized, this can reindex the summably controlled zero side of `EF_lit` directly. For `k = EF.weilTest h h`, compare `k` with `kR(y)=k(-y)` and prove the zero sums equal by a carrier equivalence instead of splitting the archimedean Bochner integral.

This is a **LEAD / HYPOTHESIS**. It is not yet W2-B or W2-C. Concrete-zeta conjugation is not a field of the abstract `ZeroConfig`, so no generic theorem may be claimed without extending the abstraction.

The old analytic route remains a fallback:

~~~text
I0  pole zeros of h -> pole zeros of EF.weilTest h h
I1  mu/gamma reflection evenness
I2  weighted gamma-channel integrability
~~~

The source route remains live in parallel.

Detailed post-green settlement: `routes/R003_ccm_bridge/W1_POST_GREEN_ZERO_SIDE_EVENIZATION_2026_09_01.md`.

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
W1 strict finite-aperture negative test                    [PROVED]
  -> W2-A W = literatureRHS(weilTest)                     [PROVED]
  -> W2-ZS concrete-zeta zero-side evenization             [OPEN / NEXT LEAD]
       rho -> 1-rho
       gammaOf sign reversal
       paperFT reflection
       legal zero-sum reindex
       half-evenized RHS equality
  -> W2-C direct W(h,h) = localizedWeilAdditiveRHS(h,h)    [OPEN]
  -> finite additive approximation / continuity            [F0-B OPEN]
  -> localizedWeilAdditiveRHS(v_N,v_N)
       = quadraticForm(canonicalSourceMatrix)              [G1-A PROVED]
  -> F1 canonical finite negative obstruction             [OPEN]
~~~

The intended next theorem should be as strong and clean as the zero-side argument supports, preferably a direct diagonal identity for every C² compactly supported concrete-zeta test rather than a W1-specialized statement.

If any of the carrier-equivalence, transform-reflection or `tsum` legality gates fails or grows unexpectedly, fall back to the explicit analytic route I0/I1/I2 -> W2-B -> W2-C. Do not silently assume `literatureRHS` linearity or gamma-integral reflection.

### Source-faithful route

The source lane has two independent prerequisite branches. They must not be drawn as one automatic sign-preserving chain.

~~~text
SOURCE INTERFACE
  S-GEOM exact aperture coordinates                     [OPEN]
  -> G1-B1A finite source sector                        [PROVED]
  -> S-IFACE / G1-B1B Haar-L²-PsiSharp-QW interface     [OPEN]
  -> G1-final QW_lambda|E_N = canonicalSourceMatrix     [OPEN]

SOURCE NEGATIVITY ENTRY
  either S-NEG:
    off-line zero -> exists fixed lambda > 1,
      inf QW_lambda < 0                                 [OPEN]
  or prove an exact W/localized-additive/QW composition
    that carries the W1 strict negative value into QW   [OPEN]

COMMON CASH-OUT
  negative ambient QW + source finite restriction
  -> G23 strict negative finite transfer                [OPEN]
  -> F1 canonical finite negative obstruction           [OPEN]
~~~

G1-B1B/G1-final are interface/restriction theorems; they do not themselves prove `Re W(h,h)<0 -> QW<0`. The two global routes should progress in parallel after W1. Select the primary F1 proof by theorem size, hypothesis cleanliness and information gain, not by historical ordering.

## 3. Exact execution queue

Semantic package IDs are authoritative. Do not reserve future PR numbers.

**Queue-order firewall:** the numeric `P` labels below are historical package identifiers, not priority. Current priority is P5/W2-ZS. P1/P2 are fallback analytic packages unless W2-ZS fails or an independent analytic cross-check is deliberately requested.

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

### P1 — W2-B explicit analytic literatureRHS reflection/evenization

**Priority:** DORMANT FALLBACK. ACTIVATE ONLY IF W2-ZS FAILS OR FOR INDEPENDENT ANALYTIC CROSS-CHECK.

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

### P2 — analytic-path W2-C diagonal W/additive bridge

**Priority:** CONDITIONAL FALLBACK AFTER P1. NOT NEXT ON THE PRIMARY INTERNAL LANE.

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


### P5 — W2-ZS concrete-zeta zero-side evenization spike

**Priority:** IMMEDIATE / HIGHEST INFORMATION GAIN

This is a bounded falsification-first spike. It attempts to bypass the explicit gamma/digamma reflection analysis by using the already-formalized concrete zeta zero symmetries and `EF_lit`'s own summability interface.

#### ZS0 — concrete conjugation transport

Theoremize the two concrete-zeta facts in the exact carrier form needed downstream:

~~~text
rho in zetaZeroConfig.carrier
  -> conj(rho) in zetaZeroConfig.carrier

zeroMult(conj rho) = zeroMult(rho).
~~~

Use `riemannZeta_conj` and `analyticOrderAt_zeta_conj`. Do not add conjugation symmetry to abstract `ZeroConfig` merely for this proof.

#### ZS1 — one-sub carrier equivalence

Compose conjugation with the existing `reflectEquiv` to obtain an involutive equivalence

~~~text
zetaOneSubEquiv :
  zetaZeroConfig.carrier ≃ zetaZeroConfig.carrier

zetaOneSubEquiv rho = 1-rho
zetaOneSubEquiv (zetaOneSubEquiv rho) = rho
mult(zetaOneSubEquiv rho) = mult(rho).
~~~

This must be a genuine subtype equivalence so reindexing is theorem-authoritative.

#### ZS2 — spectral sign reversal

Prove exactly:

~~~text
gammaOf (1-rho) = - gammaOf rho.
~~~

Smoke-test the sign convention. A sign error here invalidates the whole shortcut.

#### ZS3 — Fourier reflection

For `reflectTest k := fun y => k (-y)`, prove on the needed regularity class:

~~~text
paperFT (reflectTest k) z = paperFT k (-z).
~~~

Also theoremize preservation of C² and compact support. Use a legal whole-line change of variables.

#### ZS4 — legal EF_lit zero-sum reindex

For C² compactly supported `k`, obtain from concrete `EF_lit` the summability and equality packages for both `k` and `reflectTest k`.

Then use `Equiv.tsum_eq zetaOneSubEquiv` plus ZS1-ZS3 to prove the two zero sums equal. No `tsum_add`, `tsum_smul` or reindexing without the required summability/equivalence facts.

#### ZS5 — half-evenization through EF_lit

For

~~~text
halfEven k := fun y => (1/2 : C) * (k y + k (-y)),
~~~

prove C² + compact support and apply `EF_lit` directly. Show its zero sum equals the zero sum of `k` using the summability certificates and ZS4. Conclude

~~~text
literatureRHS (halfEven k) = literatureRHS k.
~~~

This route intentionally avoids opening the pole/prime/gamma definition of `literatureRHS`.

#### ZS6 — direct diagonal bridge

Set

~~~text
k = EF.weilTest h h.
~~~

Use W2-A and the exact definition of `CCM.localizedWeilHalfTest` to prove, if the preceding gates close,

~~~text
theorem zeta_W_self_eq_localizedWeilAdditiveRHS
    {h : R -> C}
    (hh : ContDiff R 2 h)
    (hhc : HasCompactSupport h) :
    zetaZeroConfig.W h h
      = CCM.localizedWeilAdditiveRHS h h.
~~~

Prefer this generic concrete-zeta diagonal theorem over a W1-only specialization if Lean permits it without extra assumptions.

#### Dumbassery / falsification gates

Kill or demote this shortcut immediately if any of the following occurs:

- `rho -> 1-rho` fails to preserve the exact concrete carrier or multiplicity;
- the map is not a clean involutive equivalence on the subtype;
- `gammaOf` has the opposite sign convention;
- Fourier reflection introduces conjugation or a convention factor not accounted for;
- half-evenization does not match `localizedWeilHalfTest h h` exactly;
- the proof requires illegal manipulation of divergent/totalized `tsum`s;
- the route silently uses an RH-equivalent symmetry assumption;
- theoremizing the concrete symmetry requires a larger theory than I1/I2 or the source route.

#### Internal fallback — I0/I1/I2

If W2-ZS fails for a substantive reason, return to the previous analytic plan:

~~~text
I0:
paperFT h (±I/2)=0
  -> paperFT (EF.weilTest h h) (±I/2)=0

I1:
mu (-r) = mu r

I2:
Integrable (
  fun r =>
    paperFT (EF.weilTest h h) r * (mu r : C)
).
~~~

Only after I1+I2 are theoremized may the explicit gamma-channel reflection proof split or average Bochner integrals.

#### Source parallel — S-GEOM/S-IFACE plus a separate sign entry

In parallel, preserve the source-faithful option:

~~~text
S-GEOM:
lambda := exp(L/2)
1 < lambda
sourceLength lambda = L

S-IFACE:
lock d*u, L² normalization, kappa direction,
q argument order, PsiSharp/QW normalization,
factor two and exact domain class.

S-NEG:
independent fixed-aperture negative-QW theorem,
or an exact W/localized-additive/QW theorem that carries
the W1 strict negative value into the source form.
~~~

S-GEOM/S-IFACE are infrastructure. They do not imply S-NEG. The derived W1 collar around `u=1` may be useful, but keep it marked DERIVED until separately theoremized.

#### Decision rule

Choose the zero-side internal route when ZS0-ZS6 close locally and expose F0-B as the next genuine bottleneck.

Choose the analytic fallback when the one-sub reindexing route fails but I1/I2 are local.

Choose the source route when either internal proof surface balloons while G1-B1B/G1-final, a theorem-backed source negativity entry, and G23 remain source-local.

Keep independent routes if more than one closes cleanly.

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

### Source sign gate — S-NEG or exact W/localized/QW composition

Before G23 can be used in an F1 proof, establish a theorem-backed negative ambient source value by one of two legal entries:

~~~text
A. S-NEG:
   off-line zero
     -> exists fixed lambda > 1 with inf QW_lambda < 0

B. sign-carrying identification:
   W1 negative W value
     -> exact W/localized-additive/QW composition
     -> negative QW value
~~~

G1-B1B and G1-final do not imply either entry merely by defining or restricting QW.

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

After P5 and enough source inspection to compare theorem size, select the primary proof of F1.

### Choose zero-side internal route when

- ZS0-ZS6 are green;
- the direct diagonal identity is theorem-authoritative;
- F0-B continuity/approximation remains smaller than source G23;
- approximants live in exactly the centered spaces consumed by G1-A.

### Choose analytic internal fallback when

- the zero-side reindexing fails for a local convention/interface reason;
- I1/I2 close with bounded special-function and Fourier-decay work;
- W2-B/W2-C then reduce cleanly to F0-B.

### Choose source route when

- G1-B1B maps cleanly to independently defined source objects;
- G1-final closes the actual finite source restriction;
- S-NEG or an exact W/localized-additive/QW composition supplies strict ambient source negativity;
- G23 is available with matching domain hypotheses;
- either internal route requires a larger bespoke theory.

### Keep multiple routes when

More than one closes with clean independent hypotheses. Independent proofs of F1 are high-value validation.

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
  W1 strict recentering -> support in (r,3r) inside L=4r
     DERIVED collar: support in (L/4,3L/4)

NOW
  W2-ZS concrete-zeta zero-side evenization spike
    ZS0 conjugation zero/multiplicity
    ZS1 rho -> 1-rho carrier equivalence
    ZS2 gammaOf sign reversal
    ZS3 paperFT reflection
    ZS4 summability-safe EF_lit reindex
    ZS5 half-evenized RHS equality
    ZS6 W self -> localized additive RHS

PARALLEL
  SOURCE INFRASTRUCTURE:
    S-GEOM L <-> lambda
    S-IFACE d*u/L²/kappa/q/PsiSharp/QW premise lock

  SOURCE SIGN ENTRY:
    S-NEG negative-QW theorem or exact W/localized/QW composition

FALLBACK
  INTERNAL ANALYTIC:
    I0 pole-neutrality transfer
    I1 mu/gamma evenness
    I2 weighted gamma-channel integrability
    then W2-B/W2-C

THEN
  F0-B finite approximation
  G1-A finite additive restriction [PROVED]

SOURCE ALTERNATE
  G1-B1B -> G1-final
  + theorem-backed negative-QW entry
  -> G23

TARGET
  F1:
  off-line zero -> negative canonical finite quadratic form

POST-F1
  K0 parity
  K1 aperture flow + first singularity + prime events
  K2 kernel/displacement/resolvent rigidity
  K3 arithmetic crossing exclusion

TERMINAL
  prove the demanded first canonical negative crossing cannot occur
~~~

## Standing priority question

Given everything now formally true, the next experiment or lemma should maximize mathematical information gain. Right now that is the concrete-zeta zero-side evenization spike because it can either collapse W2-B/W2-C into one small reindexing theorem or falsify that shortcut quickly and send the project back to the analytic/source alternatives.

RH remains OPEN.

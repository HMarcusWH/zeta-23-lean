# RHRC current research plan

> **Claim firewall: RH remains OPEN.**
>
> This is the living execution plan. It does not define theorem truth; Lean/compiler/CI plus the machine registries do that. This document answers what the project should do next, in what order, and why.

Current merged validation baseline:

~~~text
main = 9e899ca322116e28a56a4412d48aef0052b86fbe
tree = ad636143768dcaa4dbeb23a0ea295d7b2d6b1c9b
merged through = PR #84
PR #83 theorem head = 556be6c2b42e912c58751988c580ab4e0091822d
PR #83 merge = 7b8e0cc9abbaeff97d88ec67ada40734619a8d07
PR #84 final validated head = 1a518c9ebd408fa559c5eff281eafe5ff3b2af48
date = 2026-09-01
RH = OPEN
~~~

PR #83 exact theorem head `556be6c2b42e912c58751988c580ab4e0091822d` passed both repository workflows and merged as `7b8e0cc9...`. PR #84 then cleaned the current authority/source-route state; its exact head `1a518c9ebd408fa559c5eff281eafe5ff3b2af48` passed both repository workflows and merged to current main `9e899ca3...`. The merged theorem frontier now includes W2-ZS, the direct diagonal W/localized-additive identity, and the strict-aperture negative localized-additive witness. RH remains OPEN.

Current theorem frontier:

~~~text
W2-A genuine W/literatureRHS + pairwise summability = CLOSED / REGISTERED
W0 off-line zero -> compact C² pole-neutral negative W test = CLOSED / REGISTERED
W1 strict finite-aperture support/recentering = CLOSED / REGISTERED
W2-ZS concrete-zeta zero-side evenization = CLOSED / REGISTERED
direct diagonal W2-C endpoint:
  W(h,h) = localizedWeilAdditiveRHS(h,h) = CLOSED / REGISTERED
strict-aperture negative localized-additive witness = CLOSED / REGISTERED

NOW — F0-B FINITE APPROXIMATION / STRICT-NEGATIVITY TRANSFER
  F0-B1 boundary-flat globally C² finite Fourier approximants
  F0-B2 direct localized-additive continuity on existing legal finite vectors
  WCONT choose/prove the weakest topology that preserves the strict negative margin

PARALLEL SOURCE
  S-GEOM exact L <-> lambda bridge
  S-IFACE G1-B1B premise/normalization lock
  S-NEG independent fixed-aperture negative-QW theorem, or
        exact W/localized-additive/QW sign-carrying composition

FALLBACK INTERNAL
  I0 pole-neutrality transfer
  I1 mu/gamma reflection/evenness
  I2 weighted gamma-channel integrability
  old analytic W2-B and independent analytic proof of the W2-C endpoint

G1-A finite additive restriction = CLOSED / REGISTERED
F1 canonical finite obstruction = OPEN
RH = OPEN
~~~



The complete option inventory and historical status of individual ideas lives in RESEARCH_LEADS.md.

## 1. Plan delta after merged green W2-ZS / PR #83

PR #83 closed the zero-side shortcut proposed after W1 and did so more cleanly than the fallback analytic route expected.

**PROVED**

For every compact C² concrete-zeta test `h`,

~~~text
zetaZeroConfig.W h h
  = Zeta23.CCM.localizedWeilAdditiveRHS h h.
~~~

Production theorem:

~~~text
Zeta23.ExceptionalZero.zeta_W_self_eq_localizedWeilAdditiveRHS
~~~

No aperture, pole-neutrality, `mu`/gamma evenness, or weighted gamma-integrability hypothesis is needed.

The proof is concrete-zeta-specific. It theoremizes conjugation and `rho -> 1-rho` on the actual carrier with multiplicity, proves `gammaOf(1-rho)=-gammaOf(rho)`, proves the exact Fourier reflection convention, and reindexes the `EF_lit` zero sum under explicit `Summable` evidence. It does **not** extend generic `ZeroConfig` with new symmetry and it never opens the pole/prime/gamma decomposition of `literatureRHS`.

Composed with W1, Lean also proves the strong F0-B input:

~~~text
off-line zero
  ->
exists L>0, r>0, h,
  L=4r
  and ContDiff R 2 h
  and HasCompactSupport h
  and tsupport h ⊆ Ioo r (3*r)
  and tsupport h ⊆ Ioo 0 L
  and paperFT h ( I/2)=0
  and paperFT h (-I/2)=0
  and Re(localizedWeilAdditiveRHS h h)<0.
~~~

Registered claims:

~~~text
R003_WEIL_LOCALIZED_ADDITIVE_SELF_BRIDGE
R003_STRICT_APERTURE_NEGATIVE_LOCALIZED_ADDITIVE_WITNESS
~~~

### What changed

The old analytic W2-B route is no longer required on the shortest internal path. It remains mathematically open as a dormant independent cross-check.

The shortest theorem-backed internal route is now:

~~~text
off-line zero
  -> W0/W1                                      [PROVED]
  -> strict negative W(h,h)
  -> W2-ZS / direct diagonal bridge             [PROVED]
  -> strict negative localized additive RHS
  -> F0-B                                       [OPEN]
  -> G1-A finite additive restriction           [PROVED]
  -> F1                                         [OPEN]
~~~

Therefore **F0-B is the primary internal frontier**.

### F0-B post-green consequence

#83 makes boundary-flat finite approximants more attractive because every approximant that is genuinely compact C² can use the exact same identity as the target:

~~~text
localizedWeilAdditiveRHS(p_N,p_N) = W(p_N,p_N).
~~~

But this does not choose the approximation route for us. Two candidates remain live:

~~~text
F0-B1:
  construct globally C² boundary-flat finite Fourier approximants
  and prove W(p_N,p_N) -> W(h,h)

F0-B2:
  stay with the existing legal finite vectors from G0/G1-A
  and prove localizedWeilAdditiveRHS(v_N,v_N)
    -> localizedWeilAdditiveRHS(h,h) directly
~~~

The first bounded task is to compare these theorem surfaces and falsify hidden topology assumptions.

A permanent warning for F0-B:

~~~text
Summable(Wsummand(p_N,p_N)) for each N
  does NOT imply
a uniform summable majorant in N.
~~~

Family-level domination/continuity must be proved.

The W1 collar `tsupport h ⊂ (L/4,3L/4)` remains a strong asset for boundary-flat approximation and source localization.

Detailed post-green settlement:
`routes/R003_ccm_bridge/W2_ZS_POST_GREEN_F0B_FRONTIER_2026_09_01.md`.

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
  -> W2-ZS concrete-zeta zero-side evenization             [PROVED]
  -> W2-C endpoint:
       W(h,h)=localizedWeilAdditiveRHS(h,h)                [PROVED]
  -> strict-aperture negative localized-additive witness   [PROVED]
  -> finite approximation / continuity                     [F0-B OPEN]
  -> localizedWeilAdditiveRHS(v_N,v_N)
       = quadraticForm(canonicalSourceMatrix)              [G1-A PROVED]
  -> F1 canonical finite negative obstruction             [OPEN]
~~~

F0-B now has two legitimate bounded candidates. F0-B1 makes the approximants globally C² so #83 applies to each one; F0-B2 works directly with the existing legal finite vectors and controls the localized additive functional without requiring global C² zero extension. Do not select either route until its topology/continuity burden is inspected.

If F0-B1 is used, the load-bearing analytic statement is family-level W continuity, not merely pointwise summability. If F0-B2 is used, the load-bearing statement is direct continuity of the existing localized additive RHS on the specific finite approximation family.

The old I0/I1/I2 -> analytic W2-B route remains dormant as an independent proof/cross-check path. It is no longer on the shortest route to F1.



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

**Queue-order firewall:** the numeric `P` labels below are historical package identifiers, not priority. P5/W2-ZS is now CLOSED. The current primary frontier is F0-B. P1/P2 remain fallback analytic packages for independent cross-check only.

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

**Priority:** DORMANT INDEPENDENT ANALYTIC CROSS-CHECK. W2-ZS already proves the required diagonal endpoint without this route.

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

**Priority:** ENDPOINT PROVED VIA W2-ZS; THIS HISTORICAL ANALYTIC PROOF ROUTE REMAINS OPEN / DORMANT.

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

- W1 subsequently closed and PR #83 then closed the zero-side diagonal bridge; F0-B is now the route-general internal frontier.
- Pole neutrality survives the contraction and is preserved by the stronger #83 localized-additive cash-out.
- The internal analytic W2-B package remains available only as a dormant independent cross-check.
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


### P5 — W2-ZS concrete-zeta zero-side evenization

**Status:** CLOSED / PROVED / REGISTERED  
**Primary claim:** `R003_WEIL_LOCALIZED_ADDITIVE_SELF_BRIDGE`  
**Cash-out claim:** `R003_STRICT_APERTURE_NEGATIVE_LOCALIZED_ADDITIVE_WITNESS`  
**Exact theorem head:** `556be6c2b42e912c58751988c580ab4e0091822d`  
**Merged as:** `7b8e0cc9abbaeff97d88ec67ada40734619a8d07`

Green theorem package:

~~~text
ZS0  zeta_conj_zero / zeta_mult conjugation transport
ZS1  zetaOneSubEquiv on the concrete carrier
ZS2  gammaOf(1-rho) = -gammaOf(rho)
ZS3  paperFT reflection
ZS4  summability-safe zero-sum reindex by Equiv.tsum_eq
ZS5  zeta_literatureRHS_halfEven_eq
ZS6  zeta_W_self_eq_localizedWeilAdditiveRHS
~~~

The headline declarations have axiom surface

~~~text
[propext, Classical.choice, Quot.sound]
~~~

and the exact #83 theorem head passed both repository workflows.

### What Lean forced / revealed

The direct diagonal identity is stronger and cleaner than the fallback plan expected:

- no aperture hypothesis;
- no pole-neutrality hypothesis;
- no `mu` evenness theorem;
- no weighted gamma-channel integrability;
- no pole/prime/gamma decomposition of `literatureRHS`;
- no generic `ZeroConfig` symmetry extension.

This does **not** prove the historical analytic W2-B route. That route remains open/dormant as an independent cross-check.

### Strong W1 cash-out

PR #83 also proves:

~~~text
off-line zero
  -> strict-aperture compact C² pole-neutral h
  -> Re(localizedWeilAdditiveRHS h h) < 0.
~~~

The strong theorem preserves the explicit margin `(r,3r)` inside `L=4r`; companion wrappers expose the minimal F0-B/F1-roadmap input.

---

### F0-B — finite approximation / strict-negativity transfer

**Priority:** IMMEDIATE / HIGHEST INTERNAL INFORMATION GAIN  
**Formal status:** OPEN

Goal:

~~~text
strict negative localized-additive witness h
  -> exists finite centered coefficient vector u
     with
     Re(quadraticForm(canonicalSourceMatrix L N) u) < 0.
~~~

G1-A already proves the final finite identity. F0-B must only justify the passage from the strict negative function-level witness to some finite vector.

#### F0-B1 — boundary-flat globally C² finite approximants

For

~~~text
p(x)=sum_n u_n exp(2*pi*i*n*x/L),
~~~

force endpoint jets 0,1,2 to vanish. At coefficient level this gives the three moment constraints

~~~text
sum u_n = 0
sum n*u_n = 0
sum n^2*u_n = 0.
~~~

Candidate construction: raw centered Fourier approximant plus a fixed three-mode correction block whose coefficients tend to zero with the endpoint residuals.

If the zero extension is genuinely compact C², #83 gives for every approximant

~~~text
localizedWeilAdditiveRHS(p_N,p_N)=W(p_N,p_N).
~~~

Then it is enough to prove

~~~text
W(p_N,p_N) -> W(h,h)<0.
~~~

#### F0-B2 — direct localized-additive continuity

Avoid global C² zero extension and use the existing G0/G1-A legal finite vectors directly.

Target:

~~~text
localizedWeilAdditiveRHS(v_N,v_N)
  -> localizedWeilAdditiveRHS(h,h)<0.
~~~

This may be cheaper if direct control of the additive functional is easier than the boundary-flat/W-continuity package.

#### WCONT — load-bearing topology gate

The bounded decision spike must determine the weakest topology that actually preserves the strict negative margin.

Potential tools:

- fixed-common-support C² estimates;
- weighted Fourier decay;
- direct dominated convergence on the summable zero side;
- Route-M mollifier/tent convergence patterns.

**Critical firewall:** individual `Summable` certificates for each approximant do not provide a uniform summable majorant. Any zero-side dominated-convergence argument must prove family-level domination.

#### Regularity lead

The current canonical seed interface is C⁴ and `contDiff_poleKilled` consumes two derivatives to produce a C² pole-killed test. If raw Fourier convergence later genuinely requires a C⁴ final witness, the natural upstream target is therefore at least C⁶ seed regularity. This is a LEAD, not a theorem, and should be activated only if F0-B needs it.

#### Decision rule

Prefer F0-B1 if endpoint-flat correction plus W continuity closes with a small theorem surface.

Prefer F0-B2 if global C² zero extension or uniform W continuity balloons while direct localized-additive continuity is local.

Keep both if both close cleanly; independent F1 proofs are high-value validation.

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


## 5. F0-B / source route-selection gate before F1

### Choose F0-B1 when

- endpoint jet constraints give genuinely global compact C² zero extensions;
- the fixed reserve-mode correction coefficients tend to zero;
- a family-level W continuity theorem closes under the resulting approximation topology;
- the proof is smaller than direct additive continuity or the source G23 route.

### Choose F0-B2 when

- the existing legal finite vectors approximate the W1/#83 witness in a topology sufficient for localized-additive continuity;
- direct control avoids a larger boundary-flat zero-extension theory.

### Choose the analytic W2 fallback only for cross-validation

The old I0/I1/I2 -> W2-B route is no longer required to reach F0-B. Activate it only if an independent analytic proof of the diagonal identity is worth its theorem cost.

### Choose source route when

- G1-B1B maps cleanly to independently defined source objects;
- G1-final closes the actual finite source restriction;
- S-NEG or an exact W/localized-additive/QW composition supplies strict ambient source negativity;
- G23 is available with matching domain hypotheses;
- both F0-B candidates require a larger bespoke approximation theory.

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
- F0-B1 endpoint-flat correction / W-continuity prototypes;
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
  W2-ZS concrete-zeta zero-side evenization
  direct diagonal W2-C endpoint:
    W(h,h) = localizedWeilAdditiveRHS(h,h)
  strict-aperture negative localized-additive witness
  G1-A finite additive restriction

NOW
  F0-B finite approximation / strict-negativity transfer
    F0-B1 boundary-flat globally C² finite Fourier approximants
      + W continuity
    F0-B2 direct localized-additive continuity on existing legal finite vectors
    WCONT bounded topology/falsification decision

PARALLEL SOURCE
  S-GEOM L <-> lambda
  S-IFACE d*u/L²/kappa/q/PsiSharp/QW premise lock
  G1-B1B -> G1-final

SOURCE SIGN ENTRY
  S-NEG negative-QW theorem
  or exact W/localized/QW sign composition
  -> G23

FALLBACK / CROSS-CHECK
  I0 pole-neutrality transfer
  I1 mu/gamma evenness
  I2 weighted gamma-channel integrability
  old analytic W2-B / analytic W2-C proof route

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

Given everything now formally true, the next experiment or lemma should maximize mathematical information gain. The immediate question is no longer whether W can be identified with the localized additive functional; #83 settled that. The highest-value question is which finite-approximation topology reaches the already-proved G1-A finite quadratic form with the smallest theorem surface: boundary-flat compact C² approximation plus W continuity, or direct localized-additive continuity on the existing finite vectors.

The fastest falsifiers are:

~~~text
F0-B1:
  can endpoint-flat corrections produce legal global C² zero extensions
  with vanishing correction coefficients?

WCONT:
  can fixed-support approximants be given a family-level summable majorant
  or another quantitative W-continuity estimate?

F0-B2:
  can the localized additive functional be controlled directly on the
  existing finite vectors without rebuilding the full explicit-formula theory?
~~~



RH remains OPEN.

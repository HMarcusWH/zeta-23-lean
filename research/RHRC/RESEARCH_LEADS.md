# RHRC living research leads ledger

> **Claim firewall: RH remains OPEN.**
>
> This is a living research inventory, not a theorem registry. A lead may be promising, blocked, dormant, refuted, or promoted. Formal authority remains Lean/compiler/CI plus the machine claim and route registries.

Last full theorem/promotion review:

~~~text
main = b7d1022e33e2177c5597d008f593d3684d0ec720
theorem head = cfcf397cc8c15dbb368fbee3a161b8733061b770
synthetic merge = 19cd290510fe4fb1d253522c29644ff3e4563c03
theorem tree = 719b45162fd0814581759661f12eab16c46e1201
merged through = PR #107
RHRC #717 = SUCCESS
Permansson #490 = SUCCESS
axioms = [propext, Classical.choice, Quot.sound]
sorryAx = absent
date = 2026-09-03
RH = OPEN
~~~

Live GitHub main remains authoritative.

This file answers one persistent question:

> Given everything currently proved, experimentally observed, falsified, and historically attempted, which research ideas still exist and what is the exact status of each one?

It is intentionally broader than CURRENT_RESEARCH_PLAN.md. The plan says what to do next. This ledger remembers the whole research option space so useful ideas are not lost in old PR discussions or accidentally resurrected after falsification.

## Status vocabulary

Every entry has two logically separate statuses.

### Research status

- **ACTIVE** — currently worth theorem or experiment work.
- **TESTING** — undergoing a bounded feasibility/falsification spike.
- **READY** — prerequisites are now in place and the lead can be activated cheaply.
- **BLOCKED** — potentially useful, but a named prerequisite is missing.
- **DORMANT** — coherent, but lower priority than the active route.
- **PROMOTED** — the lead has become theorem-authoritative or consumed infrastructure.
- **SUPERSEDED** — replaced by a cleaner theorem or route.
- **REFUTED** — falsified as stated.
- **QUARANTINED** — do not reuse without an explicit changed-premise argument.

### Formal status

- **PROVED** — exact statement established by Lean/compiler/CI.
- **DERIVED** — direct consequence of proved results, not separately theoremized.
- **LEAD / HYPOTHESIS** — mathematically motivated route, not established.
- **EXPERIMENTAL SIGNAL** — numerical/search/discovery evidence only.
- **OPEN** — exact intended statement not established.
- **RH-EQUIVALENT** — theorem/audit shows the target is already RH-strength in the current framework.

Research status never upgrades formal status.

## Update law

After every meaningful green result:

1. verify the exact checked head and theorem surface;
2. update CLAIM_REGISTRY.json / ROUTE_REGISTRY.json when formal status changes;
3. update the relevant route README when route state changes;
4. update this ledger:
   - add new leads;
   - promote consumed leads;
   - block or kill failed leads;
   - resurrect old leads only when a named blocking premise changed;
5. update CURRENT_RESEARCH_PLAN.md if execution order changed;
6. keep historical settlement documents historical.

Last full theorem/promotion audit: PR #107 theorem head `cfcf397cc8c15dbb368fbee3a161b8733061b770` passed both repository workflows on exact synthetic merge `19cd290510fe4fb1d253522c29644ff3e4563c03`, with theorem tree `719b45162fd0814581759661f12eab16c46e1201`, and merged to main as `b7d1022e33e2177c5597d008f593d3684d0ec720`. CCM, ExceptionalZero, no-placeholder, RHRC regression, normalization/source firewalls and production axiom checks all passed.

---

# A. Active detector-to-additive bridge leads

## L-W0-01 — two-translate contraction to one negative Weil test

**Research status:** PROMOTED  
**Formal status:** PROVED  
**Claim ID:** `R003_NEGATIVE_WEIL_TEST_CONTRACTION`  
**Theorem:** `Zeta23.ExceptionalZero.exists_poleNeutral_negativeWeilTest_of_offLine_zero`

### What is now formally true

For every concrete zeta zero `rho0` off the critical line, Lean proves the existence of one test `h` with

~~~text
ContDiff R 2 h
HasCompactSupport h
paperFT h ( I/2) = 0
paperFT h (-I/2) = 0
Re (zetaZeroConfig.W h h) < 0.
~~~

Exact theorem-green head:

~~~text
c8112f0ad12e0b2c2f1261cea3ba7726aa04be54
~~~

merged through PR #79.

Axiom surface:

~~~text
[propext, Classical.choice, Quot.sound]
~~~

### Exact contraction

For matrix coefficients `(a,b)`, the physical test is

~~~text
h = conj(a) * k + conj(b) * T_t k.
~~~

For the existing phase witness `(‖C‖,-C)`,

~~~text
h = ‖C‖ * k - conj(C) * T_t k.
~~~

Lean proves the genuine W self-value equals the existing two-translate matrix quadratic.

### What changed

The shortest proof uses the X3 strict correlation-over-diagonal witness directly. The previously planned X4.6 determinant-converse step was unnecessary, and translation C²/support preservation already existed.

W2-A supplied the four pairwise summability certificates required before legal `tsum` recombination.

### Downstream effect

W1 subsequently closed, and PR #83 then identified the negative W value exactly with the localized additive RHS. The current internal frontier is F0-B finite approximation/continuity; the source-faithful route remains a parallel cross-check under OBS-015.

### New structural clue

Pole neutrality survives the contraction. This removes the explicit-formula pole contribution from a specialized W2-B analysis and suggests a broader witness-engineering program in which additional nuisance frequencies are killed while preserving detector visibility.


---


## L-W0-02 — strengthen constructed detector regularity if F0-B needs it

**Research status:** READY SUPPORT
**Formal status:** LEAD / HYPOTHESIS

The normalized `ContDiffBump` is smooth at arbitrary finite order, while the current X1/W0 interfaces intentionally export only C⁴ for the seed and C² after the second-order pole killer because that was the minimum required at the time.

The W1 post-green pass therefore identifies the current C² endpoint as likely an interface truncation rather than an intrinsic limitation of the constructed witness.

Potential downstream value:

- stronger Fourier decay for F0-B;
- cleaner endpoint-flat Fourier approximation;
- possible weighted-channel domination if the analytic fallback is revived.

Do not upgrade the existing W0/W1 claims without Lean proof. W2-ZS is now proved; regularity plumbing should be activated only if the live F0-B topology actually needs it.

The current source exposes `canonicalSeedTest` as C⁴ and `contDiff_poleKilled : C⁴ -> C²`, so the existing pole-killer interface costs two derivatives. If F0-B genuinely needs a C⁴ final pole-killed witness, the natural upstream target is therefore at least C⁶ seed regularity. This is a LEAD / HYPOTHESIS, not a theorem.

**Activation rule:** theoremize only the finite regularity order actually demanded by F0-B or another live theorem. Avoid a gratuitous C∞ abstraction layer.

## L-W1-01 — support recentering into one strict interior aperture

**Research status:** PROMOTED  
**Formal status:** PROVED  
**Claim ID:** `R003_STRICT_APERTURE_NEGATIVE_WEIL_TEST`  
**Theorem:** `Zeta23.ExceptionalZero.exists_strictAperture_poleNeutral_negativeWeilTest_of_offLine_zero`

### What is now formally true

For every concrete off-line zeta zero, Lean proves

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

Exact theorem declaration head:

~~~text
7abdaaf88f0e157c11049a0e65ebcb2c48fa86e2
~~~

Final validated PR #81 head:

~~~text
191e34ece05739122f362d097f9e4393cd5b9ce3
~~~

Merged main:

~~~text
1a6a286cc4aae76ef6335b85b1022ec3998614df
~~~

Axiom surface:

~~~text
[propext, Classical.choice, Quot.sound]
~~~

### What changed

The proof did not need endpoint extrema. Compact closed support was enclosed in a
symmetric open ball, then translated by twice its radius.

~~~text
tsupport h0 ⊂ (-r,r)
  -> tsupport (translateRight h0 (2r)) ⊂ (r,3r)
  -> with L=4r, support lies strictly in (0,L).
~~~

The explicit margin is stronger than the roadmap minimum.

### Downstream effect

The route-general front end is now closed. Both internal and source lanes receive the
same theorem-backed finite-aperture negative pole-neutral test.

The positive margin is a new asset for F0-B1 boundary-flat approximation.

### Falsification survived

- exact closed `tsupport`, not ordinary support;
- correct sign for `translateRight h t = h(x-t)`;
- strict positive margin, not a boundary-touching interval;
- both Fourier zeros preserved;
- W negativity preserved by exact common-translation invariance.


---

## L-W2-01 — direct W to literatureRHS(weilTest) extraction

**Research status:** PROMOTED  
**Formal status:** PROVED  
**Claim ID:** `R003_WEIL_PAIR_LITERATURE_BRIDGE`  
**Theorem:** `Zeta23.ExceptionalZero.zeta_W_literatureRHS_package`

### What is now formally true

For arbitrary complex-valued `f,g`, with `f` C² and compactly supported and `g` merely continuous and compactly supported,

~~~text
Summable (fun rho => zetaZeroConfig.Wsummand f g rho)
~~~

and

~~~text
zetaZeroConfig.W f g
  = EF.literatureRHS (EF.weilTest f g).
~~~

The asymmetric regularity is stronger than the original plan: the second leg does not need C².

### Exact green evidence

PR #77 theorem head:

~~~text
509645ad2b30288d175ff2ef5a6651839991649e
~~~

passed the CCM build, ExceptionalZero build, no-placeholder gate, RHRC regression suite, normalization/source firewalls, and axiom audit. The theorem surface depends only on `propext`, `Classical.choice`, and `Quot.sound`.

### What changed

The proof extracted the first half of `EF.prop_EF_of_lit` without aperture `L`, `nuX`, `hFk`, `hmu`, real/even hypotheses, or source `QW`. This is dependency compression: a previously buried proof fragment is now a reusable theorem and a legal summability interface.

### Downstream effect

W0 no longer had to invent or assume summability for the four pairwise two-translate terms. Historically this moved W0 ahead of W2-B; W0, W1 and the #83 W2-ZS diagonal bridge are now all proved, so F0-B is the current frontier.

### New lead

The one-sided regularity may be useful later for mixed smooth/continuous approximation arguments. This is only a LEAD; arbitrary zero-extended localized finite vectors are not generally continuous, so W2-A does not by itself close F0-B.


---


## L-W2-02 — pole-neutral reflection/evenization and gamma-channel legality

**Research status:** DORMANT INDEPENDENT ANALYTIC CROSS-CHECK
**Formal status:** OPEN

This was the immediate post-W1 plan before the zero-side reindexing shortcut was identified. PR #83 proved the required diagonal endpoint without opening this channel. The route remains mathematically valid only as an independent analytic cross-check unless a future dependency specifically needs its pole/prime/gamma decomposition.

For the actual W1 witness `h`:

~~~text
I0:
paperFT h (±I/2)=0
  -> paperFT (EF.weilTest h h) (±I/2)=0.

I1:
mu (-r) = mu r.

I2:
Integrable (
  fun r =>
    paperFT (EF.weilTest h h) r * (mu r : C)
).
~~~

I2 remains a real legality requirement for any proof that opens and splits the Bochner gamma integral. Pole neutrality does not remove it.

### Why demoted

PR #83 proved the concrete-zeta zero-side route and the generic diagonal W/localized-additive identity. Opening the gamma/digamma channel is therefore unnecessary on the shortest route to F1.

### Reactivate when

- an independent analytic proof is desired as cross-validation; or
- a later theorem needs the explicit pole/prime/gamma decomposition rather than only the already-proved diagonal identity.


## L-W2-03 — diagonal W equals localizedWeilAdditiveRHS

**Research status:** PROMOTED  
**Formal status:** PROVED  
**Claim ID:** `R003_WEIL_LOCALIZED_ADDITIVE_SELF_BRIDGE`  
**Theorem:** `Zeta23.ExceptionalZero.zeta_W_self_eq_localizedWeilAdditiveRHS`

PR #83 proves for every compact C² concrete-zeta test `f`:

~~~text
zetaZeroConfig.W f f
  = Zeta23.CCM.localizedWeilAdditiveRHS f f.
~~~

Exact theorem head:

~~~text
556be6c2b42e912c58751988c580ab4e0091822d
~~~

merged as PR #83 commit `7b8e0cc9abbaeff97d88ec67ada40734619a8d07`.

The theorem has axiom surface

~~~text
[propext, Classical.choice, Quot.sound].
~~~

### What changed

The generic diagonal identity needs only C² compact support. No aperture, pole-neutrality, `mu` evenness, gamma-channel splitting or weighted gamma-integrability hypothesis survives in the theorem statement.

The proof composes W2-A with the concrete-zeta zero-side evenization package L-W2-05. The old analytic route L-W2-02 remains open/dormant as an independent proof route, not as a prerequisite.

### Downstream effect

Composed with W1, PR #83 also proves a strict-aperture compact C² witness with

~~~text
Re(localizedWeilAdditiveRHS h h) < 0.
~~~

Therefore ambient source `QW_lambda` is no longer mandatory on the shortest route to F1. The primary internal bottleneck is F0-B.

## L-W2-04 — actual-zeta conjugation symmetry parity simplifier

**Research status:** DORMANT SMALL SPIKE  
**Formal status:** LEAD / HYPOTHESIS

PR #83 now theoremizes concrete-zeta conjugation symmetry with multiplicity as part of W2-ZS. The additional *parity simplifier conclusion* remains a lead: the proved symmetry may force the real-even detector relative correlation to be real, simplifying the phase witness to a parity-pure real combination after recentering.

**Do not reopen W0 for this.** The supporting conjugation premise is proved, but the parity simplification itself is not.


---

## L-W2-05 — concrete-zeta one-sub zero-side evenization shortcut

**Research status:** PROMOTED  
**Formal status:** PROVED  
**Consumed by claim:** `R003_WEIL_LOCALIZED_ADDITIVE_SELF_BRIDGE`

PR #83 theoremized the entire intended zero-side package on the concrete zeta carrier:

~~~text
zeta_conj_zero
zeta_one_sub_zero
zeta_mult_one_sub

zetaOneSubEquiv
zetaOneSubEquiv_mult
gammaOf_one_sub
gammaOf_zetaOneSubEquiv

paperFT_zeroSideReflectTest
zetaLiteratureZeroTsum_reflect_eq
zeta_literatureRHS_halfEven_eq
~~~

The proof uses the actual carrier equivalence `rho -> 1-rho`, multiplicity preservation, exact `gammaOf` sign reversal, Fourier reflection, and `Equiv.tsum_eq` only after explicit `Summable` evidence is available.

### What became stronger than the lead

The explicit formula remains a black box; the proof does not need to establish `mu`/gamma evenness or split the weighted gamma integral.

The result stays concrete-zeta-specific. No stronger generic `ZeroConfig` symmetry was introduced.

### Claim firewall

This promotion does **not** prove the historical analytic W2-B route. It proves the zero-side route and the resulting diagonal endpoint.

### Downstream composition

~~~text
W1 strict negative W witness
  + L-W2-03 / L-W2-05
  -> strict negative localized additive witness
  -> F0-B
  -> G1-A [PROVED]
  -> F1 [PROVED by #94].
~~~



# B. Finite-obstruction fork

## L-F0B1-01 — boundary-flat finite Fourier approximation

**Research status:** PROMOTED / PRIMARY ROUTE CLOSED  
**Formal status:** F0-B1C-A PROVED; F0-B1C-B PROVED  
**Production claims:** R003_LOCALIZED_UNIFORM_C2_APPROXIMATION; R003_BOUNDARY_FLAT_WCONT_APPROXIMATION

PR #91 closes raw centered finite Fourier approximation. PR #93 closes legal hard-window approximation in the exact WCONT topology:

~~~text
Zeta23.CCM.exists_boundaryFlatFinite_WCONT_approx
~~~

For every positive fixed aperture, strict-collar C² target and eta>0, Lean produces N>=1 and BoundaryFlatCoefficients u such that p=localizedFiniteVector L N u satisfies

~~~text
integral ||p-h|| < eta
integral ||(p-h)''|| < eta.
~~~

The complete projected vector is the legal object. OBS-016 remains a general firewall, but its primary R003 escape is PROVED.

Do not reopen Fourier density or boundary legalization on the primary route unless a downstream theorem exposes a genuine missing hypothesis.

## L-F0B2-01 — direct additive-functional continuity on legal finite vectors

**Research status:** FALLBACK / DEPRIORITIZED  
**Formal status:** OPEN

### Idea

Avoid using genuine-W continuity and target convergence directly at localizedWeilAdditiveRHS.

### Current classification

WCONT-A and #91 jointly make this route longer than the primary F0-B1 path:

~~~text
#91 raw uniform C² approximation
  -> #88 projection
  -> WCONT-A
~~~

is now theorem-backed up to one finite-dimensional projection-stability package.

### Revival condition

Revive F0-B2 only if F0-B1C-B fails at the hard-window derivative/legalization seam in a way that cannot be repaired locally.

---

## L-WCONT-01 — continuity topology for W / literatureRHS

**Research status:** PROMOTED  
**Formal status:** PROVED  
**Claim ID:** R003_WEIL_COMMON_SUPPORT_BOUND

PR #89 theorem-locks the fixed-support quantitative genuine-W estimate

~~~text
||W(f,g)||
  <= exp(Lambda) * zetaInvSqZeroMass
     * (||f||_1 + ||f''||_1) * ||g||_1
~~~

and the summability-safe diagonal cross-term / self-form perturbation package.

### What changed

The route no longer needs a family dominated-convergence theorem. The exact approximation topology is

~~~text
L1 function error
+ L1 second-derivative error
~~~

on one fixed support envelope.

### Permanent warning

Per-approximant Summable evidence is still not family domination; use the theorem-backed WCONT-A bound.

---

# C. Source-faithful parallel route

## L-G1B1B-01 — multiplicative Haar / L2 / PsiSharp / QW source correspondence

**Research status:** ACTIVE PARALLEL  
**Formal status:** OPEN

G1-B1A is PROVED and must not be rebuilt.

Minimum subgates:

1. define/theorem-lock multiplicative Haar d*u=du/u on [lambda^-1,lambda];
2. prove the exact L2 isometry under kappa;
3. formalize source q / F(u)=q(f,g)(log u) / PsiSharp;
4. prove QW(kappa f,kappa g)=PsiSharp(F) independently;
5. specialize to the already-proved finite SourceKappa sector only after the ambient theorem exists.

### Firewalls

- no implicit Lebesgue/Haar substitution;
- no factor-two or argument-order drift;
- do not define QW as the desired RHS;
- do not identify formula-level E_N with the exact L2/form-domain E_N without proof.

---

## L-G1FINAL-01 — actual QW restriction to the canonical finite matrix

**Research status:** BLOCKED BY L-G1B1B-01  
**Formal status:** OPEN

Target:

~~~text
QW_lambda restricted to E_N
  = quadraticForm (canonicalSourceMatrix (2*log lambda) N).
~~~

Must compare independently defined objects.

Proved inputs already available:

- G1-A additive finite restriction;
- direct source normalization repair;
- G1-B1A SourceKappa finite sector.

---

## L-G23-01 — minimum source core / negative-value transfer theorem

**Research status:** BLOCKED UNTIL SOURCE INTERFACE AND SIGN ENTRY MATCH  
**Formal status:** LEAD / OPEN

Port only the minimum exact source theorem needed for F1:

~~~text
strict negative ambient localized form value
  -> strict negative value on some finite E_N.
~~~

If the source naturally gives

~~~text
minEig(E_N) -> inf QW,
~~~

expose it, but do not build a larger spectral library merely for completeness.

**Critical firewall:** lower semicontinuity alone does not transport strict negativity to approximants. Need genuine form-core/form-norm approximation or the exact source minimum theorem.

### Source-sign firewall

G1-B1B and G1-final can identify the ambient source functional and its finite restriction, but they do **not** by themselves establish a negative ambient QW value from W1's `Re W(h,h)<0`. Before G23 can feed F1, the source lane needs either L-SNEG-01 below or an exact W/localized-additive/QW composition theorem.

---

## L-SNEG-01 — fixed-aperture source negative-bottom theorem

**Research status:** READY / SOURCE-CROSS-CHECK SIGN GATE  
**Formal status:** OPEN

Pin the exact source theorem before use:

~~~text
not RH
  -> exists fixed lambda > 1 with inf QW_lambda < 0
~~~

or the literal source-equivalent statement actually available.

Do not silently strengthen source hypotheses or conclusions.

---

# D. Canonical finite obstruction

## L-F1-01 — off-line zero forces a negative canonical finite quadratic form

**Research status:** PROMOTED / PRIMARY INTERNAL F1 CLOSED  
**Formal status:** PROVED  
**Claim ID:** R003_FINITE_CANONICAL_NEGATIVE_OBSTRUCTION

PR #94 proves:

~~~text
Zeta23.ExceptionalZero.
  exists_boundaryFlat_negativeCanonicalSourceQuadraticForm_of_offLine_zero
~~~

Exact endpoint:

~~~text
rho off the critical line
  -> exists L>0, N>=1, u,
       BoundaryFlatCoefficients N u
       and Re quadraticForm(canonicalSourceMatrix L N) u < 0.
~~~

The proof uses W1 + #93 + WCONT-A + F0-B1A. No source-QW interface or legacy finiteMatrix sign claim is used.

F1 is a one-way finite obstruction theorem. The finite impossibility theorem and RH remain OPEN.

# E. Post-F1 canonical finite-wall program

## L-K0F1-01 — constrained canonical sector

**Research status:** PROMOTED / PRIMARY K0-F1 CLOSED  
**Formal status:** PROVED  
**Production PR:** #96

PR #96 theorem-locks the post-F1 constrained finite algebra.

PROVED package:

~~~text
u ∈ boundaryFlatSubspace N
  <-> BoundaryFlatCoefficients N u

M_k(Du)=M_{k+1}(u)

u    kills M0,M1,M2
Du   kills M0,M1
D²u  kills M0

canonicalSourceMatrixᴴ = canonicalSourceMatrix

[D,M]v = -1 * displacementPairing(v)
for every zero-moment v
~~~

The last identity is specialized to u, Du and D²u for boundary-flat u.

Headline normalized obstruction:

~~~text
off-line zero
  -> exists L>0,N>=1,u,
       u ∈ boundaryFlatSubspace N
       and ‖u‖=1
       and Re quadraticForm(canonicalSourceMatrix L N,u)<0.
~~~

Primary declarations:

~~~text
Zeta23.CCM.mem_boundaryFlatSubspace_iff
Zeta23.CCM.centeredMoment_indexMatrix_mulVec
Zeta23.CCM.boundaryFlat_moment_flag
Zeta23.CCM.canonicalSourceMatrix_isHermitian
Zeta23.CCM.canonicalSourceMatrix_displacement_mulVec_of_moment_zero
Zeta23.CCM.boundaryFlat_canonical_displacement_package
Zeta23.ExceptionalZero.exists_unit_mem_boundaryFlatSubspace_negativeCanonicalSourceQuadraticForm_of_offLine_zero
~~~

Exact validation:

~~~text
head d628b7332e908701e85ef8ea33309e2bf548f2e5
synthetic merge 5830d75ec649f065925f5f3a1a7c823d8a5b42b9
merge 3712746a144d630ee41b89527b098e392822f2c6
tree 1d43b31bf9750375189a1ccd2e65bc0a662fc7c4
RHRC #679 SUCCESS
Permansson #452 SUCCESS
axioms [propext, Classical.choice, Quot.sound]
sorryAx absent
~~~

Do not claim D preserves V₂. Do not infer positivity from Hermitianity or one-channel displacement.

### Norm semantic firewall

The norm-one witness in #96 lives on the raw function type `Fin (...) -> ℂ`. Its norm is not the Euclidean/PiLp₂ norm used by the finite-dimensional Rayleigh API. This is now tracked as OBS-017.

---

## L-K0F1-02 — Euclidean constrained compression / negative spectral mode

**Research status:** PROMOTED  
**Formal status:** PROVED / PR #107  
**Production claims:** `R003_PARITY_CONSTRAINED_SPECTRAL_COMPRESSION`, `R003_PARITY_BAD_NEGATIVE_EIGENMODE`

PR #107 closes the constrained spectral layer.

~~~text
parity-constrained orthogonal compression P_V M|V
exact compressed/self quadratic agreement
compressed operator symmetric
ParityBad -> exists lam<0 and nonzero eigenvector v with T v = lam v
~~~

The proof uses the finite-dimensional Rayleigh infimum. Once `ParityBad p L N` is available, the spectral extraction itself does not require the positive-aperture N-flow hypotheses.

**Firewalls:** no unique negative eigenline, shell invariance, KKT, Schur, positivity or RH follows from this theorem alone.

---

## L-K0F1-03 — exact dimension / N>=2 floor

**Research status:** PROMOTED  
**Formal status:** PROVED / PR #98

PR #98 theorem-locks the rank-three moment map, finrank(boundaryFlatSubspace N)=2*N-2 for N>=1, boundaryFlatSubspace 1=bottom, the N>=2 floor for nonzero constrained witnesses, and the same exact Euclidean finrank.

Do not continue to list codimension/rank or the N>=2 floor as derived/open.

---

## L-NFLOW-01 — exact centered finite-N nesting

**Research status:** PROMOTED  
**Formal status:** PROVED / PR #100

PR #100 theorem-locks the historical centered embedding iota_{N,M}(i).val=i.val+(M-N), exact centeredIndex preservation, coherent embedding composition, exact canonical principal-block nesting, raw central zero extension, preservation of every centered moment, preservation of the represented localized finite function, Euclidean isometric zero extension, constrained-sector transport and exact canonical quadratic preservation.

The kill condition was passed: exact nesting holds; no approximate substitute was needed.

The production consequence is stronger than the original work-package target:

~~~text
off-line zero
  -> exists fixed L>0,N0>=2
  -> for every M>=N0
     exists a nonzero constrained Euclidean negative direction.
~~~

**Semantic firewall:** prefix Fin inclusion remains wrong; raw function-space norm remains distinct from the Euclidean norm; principal-block/quadratic nesting does not imply full operator intertwining or literal compressed-operator nesting.

---

## L-PARITY-01 — reversal/parity constrained split

**Research status:** PROVED FOUNDATION / ACTIVE COMPOSITION
**Formal status:** PROVED BY #102/#103; DOWNSTREAM FIXED-PARITY CONSEQUENCES OPEN

PR #102 theorem-locks reversal/moment/matrix symmetry, displacementVector oddness and exact even constrained displacement/commutator collapse.

PR #103 theorem-locks
~~~text
V_N = V_N^+ direct-sum V_N^-
D : V_N^+ ≃ₗ[ℂ] V_N^-
finrank V_N^+ = finrank V_N^- = N-1.
~~~
Euclidean parity sectors have the same dimensions and exact centered Euclidean N-flow preserves each sector.

The old composition "even u plus odd g kills the displacement pairing" is PROVED. The remaining bridge is exact quadratic parity splitting for a general negative witness.

**Firewalls:** D is not unitary; equal dimensions do not imply equal spectra; ambient commutator collapse does not imply compressed intertwining.

---

## L-PARITY-02 — D-equivalence and paired parity increments

**Research status:** PROVED FOUNDATION / ACTIVE QUOTIENT LEAD
**Formal status:** D-EQUIVALENCE #103 + D/N-FLOW COMPATIBILITY #105 PROVED

#105 proves
~~~text
D_M E_{N,M} = E_{N,M} D_N
~~~
for every raw coefficient vector.

Together with #103 this should induce an algebraic equivalence between the even and odd one-dimensional successor quotients.

**Firewall:** D is not unitary. Do not infer that D maps the orthogonal Euclidean shell to the opposite orthogonal shell.

---

## L-NFLOW-02 — first bad finite size / parity refinement

**Research status:** PROMOTED FOUNDATION / SPECTRAL CONSEQUENCES PROMOTED  
**Formal status:** PROVED / PR #105 + #107

#105 proves fixed-parity badness, least bad size, predecessor nonnegativity and the exact one-dimensional successor parity shell. #107 adds the legal parity compression, negative Rayleigh eigenmode, successor-level predecessor nonnegativity and proof that the negative mode is not inherited.

**DERIVED / OPEN FORMALIZATION:** negative shell projection, negative index exactly one, unique negative eigenline.

---

## L-FIRSTBAD-RIGIDITY-01 — intrinsic shell projection and negative index one

**Research status:** ACTIVE  
**Formal status:** DERIVED / OPEN FORMALIZATION

Let `V` be the successor parity subtype and `W` the exact centered predecessor image. Proved inputs give codimension one, `q|W >= 0`, and a negative eigenpair `Tv = lam v`, `lam<0`, with `v ∉ W`.

Immediate theorem targets:
~~~text
dim_C(W^perp) = 1
P_(W^perp) v != 0
negative index(T) = 1
unique negative eigenline
~~~

Any two-dimensional negative subspace would intersect codimension-one `W` nontrivially, contradicting `q|W >= 0`. Prove uniqueness if cheap, but do not let multiplicity API work block KKT/Schur.

---

## L-FIRSTBAD-KKT-01 — parity normal spaces and shifted Schur/Feshbach

**Research status:** ACTIVE COMPOSITION LEAD  
**Formal status:** LEAD / HYPOTHESIS

#107 supplies the actual eigenpair needed for KKT. Target normal spaces are even `span{1,d²}` and odd `span{d}`. Expected residuals:
~~~text
even: Mv = lam v + a0*1 + a2*d²
odd:  Mv = lam v + a1*d
~~~

With `V = W ⊕ Cw`, predecessor block `A >= 0`, and `lam<0`, the safe Feshbach equation is
~~~text
c - lam - b* (A - lam I)^(-1) b = 0.
~~~

Never use `A⁻¹` at zero. In the even branch, compose KKT with the proved `[D,M]v=0` and inspect the projected `d³` defect.

---

## L-K0F1-04 — first constrained Krylov block is Hankel

**Research status:** ACTIVE COMPOSITION LEAD  
**Formal status:** DERIVED / OPEN FORMALIZATION

For boundary-flat u, define

~~~text
H_ab = <D^a u, M D^b u>.
~~~

PR #96 proves that [D,M]D^b u lies in span{1} for b=0,1,2, while D^a u has zero coefficient sum for a=0,1,2.

Using self-adjointness of D and M gives the derived recurrence

~~~text
H_(a+1,b)=H_(a,b+1),  0<=a,b<=2.
~~~

Together with Hermitian symmetry this suggests that the full 4×4 block 0<=a,b<=3 is real Hankel.

This does **not** imply positivity. Real Hankel matrices may be indefinite.

**Promotion test:** theorem-lock the recurrence and determine whether, after constrained compression, it yields a non-generic determinant/minor or truncated-moment restriction.

---

## L-K1-01 — continuous aperture flow and first singularity

**Research status:** DEFERRED PENDING K0-F1F CONSTRAINED-COMPRESSION RESULT  
**Formal status:** OPEN

For fixed N:

1. prove continuity of canonicalSourceMatrix L N for L>0;
2. prove prime-power birth terms vanish at entry L=log q, eliminating an apparent matrix jump;
3. rederive the derivative jump in the canonical normalization;
4. obtain a positive anchor for the same N;
5. define the first L* where lambda_min crosses zero.

### E2 prediction

The derivative jump is expected to be rank one in

~~~text
J = 1 1^T
~~~

with coefficient proportional to

~~~text
-2 Lambda(q)/(sqrt(q) log q).
~~~

This is a LEAD until rederived on canonicalSourceMatrix.

---

## L-K2-01 — singular kernel/displacement rigidity

**Research status:** DEFERRED PENDING K0-F1F CONSTRAINED-COMPRESSION RESULT  
**Formal status:** LEAD / OPEN

PROVED structural input:

~~~text
[D,M] = g 1^T - 1 g^T.
~~~

At M u=0, theorem-lock the exact sign/orientation of

~~~text
M(Du) = -g (1^T u) + 1 (g^T u).
~~~

After parity:

~~~text
u even: g^T u = 0
u odd:  1^T u = 0.
~~~

Do not assume one-dimensional kernel.

---

## L-K2-02 — parity-block distinguished resolvents

**Research status:** DEFERRED PENDING K0-F1F CONSTRAINED-COMPRESSION RESULT  
**Formal status:** LEAD / HYPOTHESIS

Candidate scalar resolvents:

~~~text
m_even(z) = <1, (M_even-z)^(-1) 1>
m_odd(z)  = <g, (M_odd-z)^(-1) g>.
~~~

The displacement equation couples a zero mode in one sector to one distinguished forcing vector in the other.

**Promotion test:** must create an actual sign/crossing restriction, not generic low-displacement-rank folklore.

---

## L-K3-01 — arithmetic crossing engine

**Research status:** DORMANT UNTIL K2  
**Formal status:** LEAD / HYPOTHESIS

Composition candidates:

- E2 canonical prime-event rank-one flow;
- E5 resolvent / Sherman-Morrison / determinant-lemma / spectral-measure analysis;
- E7 parity-reduced barycentric zero-mode equation;
- T23 first-crossing degeneracy classification;
- Schur / LDL / principal-minor sign constraints.

### Terminal research question

What structure does the **first** canonical zero crossing have that an arbitrary singular Hermitian matrix does not, and can prime-event, parity, displacement and resolvent laws make that state impossible?

A bare universal theorem "canonicalSourceMatrix is PSD for all L,N" is likely RH-strength once F1 and the reverse direction are available. Do not misclassify that as a cheap finite lemma.

---

# F. Distinguished all-ones channel

## L-ONES-01 — dangerous motion may concentrate in the 1 / g channels

**Research status:** ACTIVE COMPOSITION HYPOTHESIS  
**Formal status:** mixed PROVED inputs + LEAD conclusion

Repeated independent appearances of the all-ones direction:

- H2/H2+ finite discrepancy collapsed to a scalar multiple of J=11^T before Route M killed the scalar defect;
- canonical displacement is exactly g1^T-1g^T;
- expected E2 prime births are rank one in J;
- reversal parity makes 1 even and odd vectors orthogonal to it;
- E5 naturally studies <1,(M-z)^-1 1>.

### Current hypothesis

The finite-wall mechanism may not be "low displacement rank proves RH." It may be that normalization history, prime births, parity and exact displacement concentrate the first dangerous spectral motion into a tiny distinguished channel.

### Fastest test

First build the Euclidean compressed negative spectral mode and theorem-lock/falsify the 4×4 Krylov-Hankel recurrence. Reopen the canonical E2 derivative jump only if the compressed object still lacks a sign/crossing restriction.

---

# G. E1-E7 resurrection ledger

## L-E1-01 — source quotient / finite information recovery

**Research status:** DORMANT-BUT-VALID  
**Formal status:** LEAD / HYPOTHESIS

No theorem refuted the finite-information recovery idea; full 2N+1 source dimension is now locked.

**Resume only if:** the obstruction becomes information sufficiency/recovery rather than sign transfer.

---

## L-E2-01 — prime cutoff / event flow

**Research status:** DEFERRED UNTIL K0-F1F / ACTIVE WHEN K1 REOPENS  
**Formal status:** LEAD

Canonical normalization removed the old sign-authority ambiguity. Re-derive the prime-power derivative jump on canonicalSourceMatrix.

**Kill any formula** that only holds for legacy finiteMatrix.

---

## L-E3-01 — finite jet / recurrence / Prony machinery

**Research status:** ACTIVE SUPPORT FOR F0-B1  
**Formal status:** LEAD

Use only the minimal moment algebra required by the codimension-three endpoint constraints. Do not revive the full historical reconstruction program without additional leverage.

---

## L-E4-01 — parity / extremal spectrum

**Research status:** ACTIVE DOWNSTREAM OF K0-F1F  
**Formal status:** LEAD

Full complex finite space is now theorem-locked. Use parity to split channels and kernels.

**Moustache warning:** universal odd-sector positivity is RH-strength territory; parity is a decomposition tool, not an assumed sign theorem.

---

## L-E5-01 — resolvent / spectral measure / Weyl updates

**Research status:** ACTIVE AT K2/K3  
**Formal status:** LEAD

Rank-one J events plus first singularity and distinguished displacement channels create an exact resolvent problem.

**Archive again if:** it yields only determinant identities with no sign/crossing restriction.

---

## L-E6-01 — finite XiHat / entire-function route

**Research status:** DORMANT ALTERNATE  
**Formal status:** LEAD

Still coherent for a longer determinant/Hurwitz/Xi convergence route.

**Resume only if:** the F1/finite-wall route stalls or a stable local-uniform finite entire-function convergence theorem appears.

---

## L-E7-01 — barycentric arithmetic eigenfunction equation

**Research status:** CONDITIONAL K3 SPIKE  
**Formal status:** LEAD

Zero eigenvalue plus parity may make the equation more rigid than in its original generic form.

**Immediate falsifier:** prove whether the proposed equation contains information beyond M u=0. Kill it if tautological.

---

## T21 — Constraint-Lock / Premise-Escape Audit

**Research status:** RECOVERED PROJECT-HISTORY DISCOVERY TOOL
**Formal status:** LEAD / TOOL; NO LEAN CLAIM

Recovered from the earlier ESET theorem-groundwork cross-project review. For any proposed closure, identify which premise carries the real obstruction and test whether the route discharges it or merely relocates an equally strong premise.

Use on fixed-parity, KKT, source-interface and positivity candidates to expose hidden RH-equivalent assumptions, vacuous coercivity hypotheses and circular sign conditions.

---

## T22 — Structured-Ray Coercivity/Inertia Falsifier

**Research status:** RECOVERED PROJECT-HISTORY DISCOVERY TOOL
**Formal status:** LEAD / TOOL; NO LEAN CLAIM

Recovered from the earlier ESET theorem-groundwork cross-project review. Attack proposed universal positivity/coercivity/inertia claims on structured one-parameter or low-dimensional rays preserving the relevant constraints before expensive formalization.

A counterexample kills the candidate; ray survival is only an EXPERIMENTAL SIGNAL.

---

# H. Alternate / comparator routes

## L-R002-01 — R002 negative-index masking branch

**Research status:** SEPARATE ACTIVE DISCOVERY ROUTE  
**Formal status:** block-level negativity PROVED; full window visibility OPEN

PR #66 settled the generic smooth-taper R002 object as SPECIALIZATION_ONLY relative to canonical CCM. Pair-level signed off-line negativity remains a useful adversarial motif, but masking is an R002 problem, not an F1 prerequisite.

---

## L-BOMB-01 — Bombieri finite-inertia comparator / possible future duality

**Research status:** COMPARATOR ONLY  
**Formal status:** no CCM transfer theorem

Bombieri truncates the zero-index multiset; CCM truncates deterministic Fourier characters. Preserve Bombieri as a sanity check on finite-negativity persistence and a possible future operator-duality lead.

**Forbidden:** direct identification of the two finite matrices.

---

## L-CONNES-01 — finite operator / Xi determinant route

**Research status:** DORMANT ALTERNATE  
**Formal status:** OPEN

Finite self-adjoint perturbations and real-zero characteristic transforms remain conceptually relevant, but local-uniform/determinant-to-Xi convergence is a separate long route.

Resume only if the fixed-aperture finite-obstruction route stalls or new source work closes the missing convergence theorem.

---

## L-SUZUKI-01 — fixed-aperture localized-bottom route

**Research status:** ACTIVE ALTERNATE / CROSS-CHECK  
**Formal status:** exact project transfer OPEN

Keep the exact Suzuki not-RH -> negative localized-bottom interface separately named. If Suzuki and the project's canonical detector route both independently imply F1 after G1/G23, that is strong architectural validation.

Do not silently merge Suzuki's operator with CCM without an exact map theorem.

---

## L-X46-01 — quantitative detector aperture / bandwidth control

**Research status:** ACTIVE AUXILIARY  
**Formal status:** detector-sequence completeness PROVED; quantitative aperture relation OPEN

X4.6 gives eventual visibility in an explicit radius sequence but still allows detector-dependent translation aperture.

Quantify support width / required aperture if useful for choosing L,N in F0-B or relating detector complexity to finite Fourier bandwidth.

---

## L-R004J-01 — analytically specified Jacobi/prolate generator

**Research status:** DORMANT-BUT-VALID  
**Formal status:** displacement PROVED; generator route OPEN

The exact displacement theorem survived. The fitted small-commutator -> eigenvector-convergence story did not.

Revival requirements:

1. analytically specified generator;
2. absolute commutator estimate;
3. non-collapsing/simple spectral-gap theorem;
4. only then perturbative eigenspace control.

---

# I. Promoted / consumed leads retained for lineage

These are no longer open leads, but they are kept here because future work repeatedly depends on the fact that they were once uncertain and are now theorem-authoritative.

## P-X46 — explicit countable canonical detector bank

**Research status:** PROMOTED  
**Formal status:** PROVED

Every hypothetical off-line zero forces a negative determinant for one explicitly indexed canonical pole-killed detector and some nonnegative aperture.

Primary endpoint:
Zeta23.ExceptionalZero.exists_canonicalRadiusSequence_negativeDeterminant_of_offLine_zero.

---

## P-H2 — scalar/J finite discrepancy collapse

**Research status:** PROMOTED / CONSUMED  
**Formal status:** PROVED project infrastructure

The finite dictionary discrepancy collapsed to one N-independent scalar times J=11^T; Route M then proved the scalar defect zero.

This remains historically important because it first exposed the recurring all-ones channel.

---

## P-ROUTEM — literal tent explicit-formula extension

**Research status:** PROMOTED / CONSUMED  
**Formal status:** PROVED

The C2 mollifier architecture and channel-by-channel limit proof legalized the literal canonical tent and closed the finite dictionary bridge without applying EF_lit directly to the nonsmooth tent.

---

## P-G1A — additive finite restriction

**Research status:** PROMOTED / ACTIVE INFRASTRUCTURE  
**Formal status:** PROVED_UNCONDITIONAL

Claim:
R003_LOCALIZED_ADDITIVE_RHS_RESTRICTION.

Production theorem:
Zeta23.CCM.localizedWeilAdditiveRHS_finiteVector_eq_cutoffFreeQuadraticForm.

---

## P-NORM — canonical source normalization repair

**Research status:** PROMOTED / ACTIVE INFRASTRUCTURE  
**Formal status:** PROVED_UNCONDITIONAL

Canonical sign-authoritative object:

~~~text
canonicalSourceMatrix
 = cutoffFreeMatrix
 = sourceEq44Matrix
 = dictionaryMatrix
 = zeroSideMatrix  (positive-aperture bridge).
~~~

Legacy object:

~~~text
legacyPrintedMatrix = finiteMatrix.
~~~

They differ by an exact scalar identity shift. Shift-sensitive spectral work must use the canonical object.

---

## P-G1B1A — finite kappa/source-sector bridge

**Research status:** PROMOTED / ACTIVE INFRASTRUCTURE  
**Formal status:** PROVED_UNCONDITIONAL

Claim:
R003_SOURCE_KAPPA_FINITE_SECTOR.

Production theorem:
Zeta23.CCM.sourceKappaFiniteVector_eq_sourceFiniteVector.

Haar/L2/PsiSharp/QW remain outside this theorem.

---

## P-DISP — canonical rank-two displacement

**Research status:** PROMOTED / ACTIVE INFRASTRUCTURE  
**Formal status:** PROVED_UNCONDITIONAL

~~~text
[D,M] = g 1^T - 1 g^T
rank([D,M]) <= 2
~~~

on canonicalSourceMatrix.

This proves structure, not positivity or RH.

---

# J. Refuted / quarantined leads

The authoritative failure details live in DEAD_ROUTES.md and OBSTRUCTION_LEDGER.md. They are mirrored here so the lead inventory is complete.

## Q-001 — TightMult-visible scalar improvement

**Research status:** QUARANTINED  
**Formal status:** blocked by PROVED OBS-001

Cannot improve RH using only the same TightMult-visible scalar compression statistics. Needs a genuinely new information channel.

---

## Q-002 — fixed local-ordinal zeta mapping

**Research status:** REFUTED / HISTORICAL  
Rejected in the earlier CCM campaign.

---

## Q-003 — curvature_gap W96 hidden field

**Research status:** REFUTED  
Rejected by matched adversarial null and transfer failure.

---

## Q-004 — MV square-root-cancellation shortcut for R001

**Research status:** QUARANTINED  
Exponent bookkeeping leaves the required detection beyond the achieved scale. Revival would need to remove the MV additive penalty using information already of RH/zero-density strength.

---

## Q-005 — independent scalar arithmetic closure of R001

**Research status:** QUARANTINED  
**Formal status:** RH-EQUIVALENT

R001_PRIME_UPPER is Lean-proved equivalent to the critical-line statement in the current framework.

---

## Q-006 — killed R002 observable families

**Research status:** REFUTED / QUARANTINED

- odd cubic tr G-tilde^3;
- L2 aperture coherence;
- full-diagonal majorization.

See DEAD_ROUTES.md / R002 feasibility settlement.

---

## Q-007 — legacy finiteMatrix = ambient QW restriction

**Research status:** FORBIDDEN

PRs #71/#73 established the canonical source normalization. Any actual source restriction theorem must land on canonicalSourceMatrix.

---

## Q-008 — generic R002 taper-grid = canonical CCM

**Research status:** REFUTED AS GENERIC IDENTITY / SPECIALIZATION_ONLY

The hard-window basis relation is real, but the production smooth-taper object is distinct.

---

## Q-009 — Bombieri finite truncation = deterministic CCM band

**Research status:** QUARANTINED

Different finite coordinates, dimensions and truncation laws. Requires a new exact transfer theorem before reuse.

---

## Q-010 — fitted small commutator -> eigenvector convergence

**Research status:** REFUTED AS STATED

The fitted generator's spectral gaps collapse in tested cases. See L-R004J-01 for the only legitimate revival conditions.

---

## Q-011 — legacy absolute spectrum as canonical source spectrum

**Research status:** FORBIDDEN

Scalar identity shifts do not preserve absolute eigenvalues, PSD, inertia, lower bounds, trace or determinant.

---

# K. Methodology tools that govern lead evaluation

These are not RH theorem inputs. They are research-control tools preserved from the wider project methodology.

## T21 — constraint-lock / premise-escape audit

Use at source interfaces and any scope change. Solve all declared interface constraints first and classify whether the intended target is actually compatible with them.

Useful outputs include:

- CONSISTENT_EXACT_TARGET;
- SECTOR_RESTRICTED;
- PREMISE_CONFLICT;
- NEEDS_POLARIZATION;
- NEEDS_ALTERNATE_CORE;
- NEEDS_COMPACT_INTERFACE;
- QUARANTINED_CIRCULAR.

---

## T22 — structured-ray coercivity / inertia falsifier

Attack proposed global coercivity, norm-equivalence, projection-stability and generalized-eigenvalue estimates on normalized high-frequency families before formalizing them.

A single exact/asymptotic counterfamily kills the proposed architecture.

---

## T23 — sign-crossing / degeneracy locator

When a theorem-authoritative continuous quantity changes sign, treat the first crossing/degeneracy surface as a structured object. In the RH program this is especially relevant to K1-K3.

Discovery output from T23 is not theoremhood.

---

# L. Standing research questions

After every meaningful green result, revisit:

1. What became possible that was not possible before?
2. Which assumptions disappeared or can now be weakened?
3. Which dead route had exactly that missing prerequisite?
4. Can two or more proved results compose into a qualitatively stronger restriction?
5. Can we attack the admissible counterexample space rather than RH directly?
6. What is the cheapest falsifier for the most promising new clue?
7. Does the result compress the dependency graph?
8. Is a proposed "next lemma" secretly RH-equivalent?
9. Are we working on the canonical sign-authoritative object?
10. Does any conclusion depend on an unproved identification between distinct finite/operator objects?

RH remains **OPEN**.

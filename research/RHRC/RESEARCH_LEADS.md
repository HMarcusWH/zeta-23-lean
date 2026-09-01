# RHRC living research leads ledger

> **Claim firewall: RH remains OPEN.**
>
> This is a living research inventory, not a theorem registry. A lead may be promising, blocked, dormant, refuted, or promoted. Formal authority remains Lean/compiler/CI plus the machine claim and route registries.

Last full theorem/promotion review:

~~~text
main = 8960b80b4a871bd86f94509dfa872ecc6939b0cd
tree = 956601c77d1e9f32bab339dbbb81130296d1b5c7
merged through = PR #80
W1 Stage-A theorem-green head = 7abdaaf88f0e157c11049a0e65ebcb2c48fa86e2
date = 2026-09-01
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

Last full theorem audit: PR #79 W0 theorem head `c8112f0ad12e0b2c2f1261cea3ba7726aa04be54`, merged to main as `3e39ce86d27a4c642a1e0364f1954968ce22f1f4`. Exact-head CI passed the CCM and ExceptionalZero builds, no-placeholder gate, RHRC suite, normalization/source firewalls and independent verification workflow.

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

W1 is now the unique route-general frontier. The internal and source-faithful routes can both consume the same concrete negative function-level obstruction after recentering.

### New structural clue

Pole neutrality survives the contraction. This removes the explicit-formula pole contribution from a specialized W2-B analysis and suggests a broader witness-engineering program in which additional nuisance frequencies are killed while preserving detector visibility.


---

## L-W0-02 — promote stronger canonical detector regularity only if required

**Research status:** READY SUPPORT  
**Formal status:** LEAD / HYPOTHESIS

The Mathlib canonical bump is smooth, while the current theorem package only exports canonicalSeedTest as C4 and canonicalPoleKilledTest as C2 because that was sufficient for X1-X4. If the source route requires stronger regularity, theoremize only the exact finite regularity required by the source theorem.

**Stop condition:** if C-infinity plumbing is disproportionately expensive, keep C2 and prefer the internal additive route or prove only the source-required finite order.

---

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

Exact Stage-A theorem-green head:

~~~text
7abdaaf88f0e157c11049a0e65ebcb2c48fa86e2
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

W0 no longer has to invent or assume summability for the four pairwise two-translate terms. This is why W0 now outranks W2-B as the immediate global target.

### New lead

The one-sided regularity may be useful later for mixed smooth/continuous approximation arguments. This is only a LEAD; arbitrary zero-extended localized finite vectors are not generally continuous, so W2-A does not by itself close F0-B.


---

## L-W2-02 — pole-neutral reflection/evenization and gamma-channel legality

**Research status:** ACTIVE / INTERNAL ROUTE PROBE  
**Formal status:** OPEN

### Corrected post-W1 target

Do not treat reflection symmetry as the only remaining analytic gate.

For the actual W1 witness `h`, first prove:

~~~text
I0:
paperFT h (±I/2)=0
  -> paperFT (EF.weilTest h h) (±I/2)=0.
~~~

Then isolate the archimedean channel through the existing density `mu`.

Target:

~~~text
I1:
mu (-r) = mu r.
~~~

But also prove the separate legality condition:

~~~text
I2:
Integrable (
  fun r =>
    paperFT (EF.weilTest h h) r * (mu r : C)
).
~~~

### Why I2 matters

The existing explicit-formula proof carries this weighted integrability hypothesis
explicitly. Bochner `integral_add` requires integrability. Reflection/evenization must
not reproduce the old totalized-tsum mistake at the integral level.

### What pole neutrality does close

The pole contribution vanishes on the load-bearing class.

The prime term is structurally reflection invariant because it occurs as

~~~text
k(log n) + k(-log n).
~~~

### Fastest falsification

Attempt I1 and I2 before building generic literatureRHS linearity.

If weighted gamma/mu integrability requires a large new special-function/Fourier-decay
theory, downgrade the internal route and compare directly against G1-B1B/G23.


---

## L-W2-03 — diagonal W equals localizedWeilAdditiveRHS

**Research status:** ACTIVE  
**Formal status:** OPEN

### Target

On the exact admissible class,

~~~text
zetaZeroConfig.W f f
  = Zeta23.CCM.localizedWeilAdditiveRHS f f.
~~~

On the diagonal, localizedWeilHalfTest is half the evenization of EF.weilTest f f. L-W2-01 plus L-W2-02 should therefore supply the bridge.

### Why it matters

G1-A is already PROVED:

~~~text
localizedWeilAdditiveRHS(localizedFiniteVector u,
                         localizedFiniteVector u)
  = quadraticForm(cutoffFreeMatrix) u
  = quadraticForm(canonicalSourceMatrix) u.
~~~

If L-W2-03 closes, ambient QW may no longer be mandatory on the shortest route to F1.

---

## L-W2-04 — actual-zeta conjugation symmetry parity simplifier

**Research status:** DORMANT SMALL SPIKE  
**Formal status:** LEAD / HYPOTHESIS

Actual zeta has conjugation symmetry in addition to the reflection already built into ZeroConfig. If theoremized with multiplicity, it may force the real-even detector relative correlation to be real, simplifying the phase witness to a parity-pure real combination after recentering.

**Do not block W0 on this.** The current ZeroConfig abstraction does not carry this symmetry.

---

# B. Finite-obstruction fork

## L-F0B1-01 — boundary-flat finite Fourier approximation

**Research status:** TESTING CANDIDATE  
**Formal status:** OPEN

### Idea

For

~~~text
p(x) = sum_n u_n exp(2*pi*i*n*x/L),
~~~

global C2 zero extension requires periodic endpoint value and first two derivatives to vanish, yielding the three coefficient moment constraints

~~~text
sum_n u_n       = 0
sum_n n u_n     = 0
sum_n n^2 u_n   = 0.
~~~

For a smooth h supported strictly inside (0,L), approximate h by a centered trigonometric polynomial and correct the three small endpoint jet errors with a fixed three-mode correction block.

### Why plausible

The constrained subspace has codimension three, and the low-mode jet matrix for modes -1,0,1 is algebraically invertible for L>0.

### Main blocker

Need convergence in a topology strong enough that W(p_N,p_N) -> W(h,h), not merely L2 convergence.

### Composition

Resurrects only the minimal E3 finite moment/jet algebra.

### Stop condition

Kill this route if endpoint correction fails to converge in the W-controlling topology or if the required analytic theory becomes larger than the source G23 theorem.

---

## L-F0B2-01 — direct additive-functional continuity on legal finite vectors

**Research status:** TESTING / CURRENTLY PREFERRED F0 SPIKE  
**Formal status:** OPEN

### Idea

Avoid requiring localizedFiniteVector itself to be globally C2. G1-A already proves the canonical matrix identity on these legal finite vectors using the legalized dictionaryTest.

Target convergence only at the additive functional level:

~~~text
localizedWeilAdditiveRHS(v_N,v_N)
  -> zetaZeroConfig.W(h,h)
~~~

for finite Fourier approximants v_N -> h in a suitable topology.

### Potential advantage

Could bypass the entire boundary-flat C2 zero-extension construction.

### Burden

Control the pole evaluations, finite prime term and archimedean gamma-weighted Fourier integral along the special dictionary/autocorrelation family.

### Stop condition

If this balloons into weighted Sobolev/form-core theory larger than G23, prefer the source route.

---

## L-WCONT-01 — continuity topology for W / literatureRHS

**Research status:** BLOCKED ON CHOOSING F0 ROUTE  
**Formal status:** OPEN

Find the weakest common-support topology that yields

~~~text
W(p_N,p_N) -> W(h,h)
~~~

with a quantitative enough bound to preserve a fixed negative margin.

Candidate approaches:

- C2/common-support explicit-formula estimate;
- weighted Fourier decay;
- direct dominated convergence on the zero sum;
- reuse of Route-M mollifier/tent convergence patterns.

**T22 warning:** high-frequency approximants can converge in a weak norm while the gamma/log-weighted channel remains uncontrolled.

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

**Research status:** BLOCKED UNTIL SOURCE INTERFACE MATCHES  
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

---

## L-S0-01 — fixed-aperture source negative-bottom theorem

**Research status:** DORMANT / SOURCE-CROSS-CHECK  
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

**Research status:** BLOCKED BUT HIGHEST PRE-v2.0 TARGET  
**Formal status:** OPEN

Exact intended theorem:

~~~text
(exists rho : zetaZeroConfig.carrier, (rho : C).re != 1/2)
  -> exists L : R, 0 < L
     and exists N : Nat
     and exists u : Fin (2*N+1) -> C,
       Re (quadraticForm (canonicalSourceMatrix L N) u) < 0.
~~~

No legacy finiteMatrix, numerical surrogate, hidden QW definition, or normalization shortcut.

### Possible proof routes

- internal: W0/W1 + W2 + F0-B + G1-A;
- source: W0/W1 + G1-B1B + G1-final + G23;
- independent Suzuki/source route if exact hypotheses match.

A second independent proof of F1 would be unusually valuable.

### Promotion rule

When F1 becomes green, perform a full Post-Green Research Pass before beginning the terminal finite-wall program. F1 green is the threshold for a new external roadmap v2.0, not a proof of RH.

---

# E. Post-F1 canonical finite-wall program

## L-K0-01 — Hermitian / reversal / parity package

**Research status:** READY AFTER F1; cheap pieces may be explored earlier  
**Formal status:** OPEN, with structural PROVED inputs

Target package:

- canonical matrix real symmetric or Hermitian in the exact coefficient convention;
- M_{-n,-m}=M_{n,m};
- reversal operator R with RM=MR;
- centered index D anticommutes with R;
- canonical displacement vector g is odd;
- all-ones vector 1 is even;
- odd vectors have coefficient sum zero.

### Why it matters

Splits the finite space into parity sectors and turns the exact rank-two displacement relation into much smaller forcing channels.

---

## L-K1-01 — continuous aperture flow and first singularity

**Research status:** BLOCKED UNTIL F1 / K0  
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

**Research status:** BLOCKED UNTIL K0/K1  
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

**Research status:** BLOCKED UNTIL K0/K1  
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

Theoremize K0 and the canonical E2 derivative jump, then derive the parity-block resolvent equations and check whether they imply anything stronger than a re-expression of M u=0.

---

# G. E1-E7 resurrection ledger

## L-E1-01 — source quotient / finite information recovery

**Research status:** DORMANT-BUT-VALID  
**Formal status:** LEAD / HYPOTHESIS

No theorem refuted the finite-information recovery idea; full 2N+1 source dimension is now locked.

**Resume only if:** the obstruction becomes information sufficiency/recovery rather than sign transfer.

---

## L-E2-01 — prime cutoff / event flow

**Research status:** READY / ACTIVE AT K1  
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

**Research status:** ACTIVE AT K0  
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

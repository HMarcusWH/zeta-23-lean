# R003 — CCM / finite Weil bridge

Status: **ACTIVE DISCOVERY ROUTE. RH OPEN.**

**Scope note after merged PRs #83/#84:** current main is `9e899ca322116e28a56a4412d48aef0052b86fbe` (tree `ad636143768dcaa4dbeb23a0ea295d7b2d6b1c9b`). PR #83 theorem-locked W2-ZS on exact head `556be6c2b42e912c58751988c580ab4e0091822d` and merged it as `7b8e0cc9abbaeff97d88ec67ada40734619a8d07`; PR #84 then cleaned the authority/source-sign state and passed both workflows before merging to current main.

The shared function-level route is now theorem-locked through the localized additive functional:

~~~text
off-line zero
  -> W0 negative compact C² pole-neutral W witness
  -> W1 strict aperture margin
  -> W2-ZS:
       W(h,h)=localizedWeilAdditiveRHS(h,h)
  -> strict negative localized additive witness.
~~~

Registered claims:

~~~text
R003_WEIL_LOCALIZED_ADDITIVE_SELF_BRIDGE
R003_STRICT_APERTURE_NEGATIVE_LOCALIZED_ADDITIVE_WITNESS
~~~

The W2-ZS proof theoremizes concrete-zeta conjugation, the actual `rho -> 1-rho` carrier equivalence with multiplicity, `gammaOf` sign reversal, exact Fourier reflection, and summability-safe zero-sum reindexing. It does not open the pole/prime/gamma decomposition and does not extend generic `ZeroConfig`.

The previous I0/I1/I2 analytic W2-B route remains OPEN / DORMANT as an independent cross-check. It is not a prerequisite for the now-proved diagonal endpoint.

The immediate internal frontier is **F0-B finite approximation / strict-negativity transfer**. Two bounded candidates remain live: boundary-flat global C² finite approximants plus W continuity, and direct localized-additive continuity on the existing legal finite vectors. Family-level domination/continuity is the load-bearing issue.

Source infrastructure `S-GEOM`/`S-IFACE` remains active in parallel, while strict source negativity is a separate `S-NEG`/sign-composition gate under OBS-015.

This README is the living route SSOT for the merged repository. PR-specific settlement files in this directory are historical records; they do not override live Lean/CI or this current route state.

Historical post-W1 settlement:
[`W1_POST_GREEN_ZERO_SIDE_EVENIZATION_2026_09_01.md`](W1_POST_GREEN_ZERO_SIDE_EVENIZATION_2026_09_01.md).

Current post-W2-ZS settlement:
[`W2_ZS_POST_GREEN_F0B_FRONTIER_2026_09_01.md`](W2_ZS_POST_GREEN_F0B_FRONTIER_2026_09_01.md).

## Objective

Build an exact, source-faithful chain from finite Fourier test functions to the fixed-aperture localized Weil form, and only then use a legitimate variational/core theorem to transport fixed-aperture spectral information.

The critical endpoint is not a finite matrix formula by itself. It is the actual restriction theorem

```text
QW_lambda restricted to E_N = canonicalSourceMatrix.
```

## Current canonical object map

The direct source finite matrix authority is

```text
canonicalSourceMatrix
  = cutoffFreeMatrix
  = sourceEq44Matrix
  = dictionaryMatrix.
```

For positive aperture the existing zero-side bridge also identifies the actual finite zeta zero-side matrix with the cutoff-free/canonical matrix.

The historical printed normalization is

```text
legacyPrintedMatrix = finiteMatrix.
```

with exact scalar-shift relation

```text
canonicalSourceMatrix
  = legacyPrintedMatrix
    + 2*legacyPrintedCorrection(L)*I.
```

No route document may identify `finiteMatrix` directly with ambient `QW_lambda|E_N`.

Machine-readable current map: `CCM_CANONICAL_OBJECT_MAP_v3.json`. Version 2 is retained as the historical post-#73 snapshot.

## Why the normalization firewall exists

The route history matters.

- PR #28 refuted the naïve no-shift CCM/Weil identification and localized the problem to the diagonal archimedean term.
- PR #29 identified the scalar diagonal shift numerically/structurally and proved displacement-transfer algebra.
- PR #33 pinned an independent cutoff-free source oracle.
- PR #65 formalized the cutoff-free matrix and proved its relation to the zero-side/dictionary matrix.
- PR #71 theorem-locked the direct Section-4 equation-(4.4) finite source matrix and exposed the later printed equation-(4.11)/(4.14) normalization inconsistency.
- PR #73 repaired repository semantics: canonical direct-source labels now point to the cutoff-free object; historical printed objects remain frozen.

The lesson is permanent: finite formula agreement does not by itself close source normalization, carrier, measure, functional, and restriction semantics.

## Closed theorem ladder on merged main

### Finite dictionary / explicit-formula layer

Closed work includes:

- finite divided-difference/source calculus;
- finite Guinand--Weil dictionary;
- deterministic dictionary RHS identity;
- literal-tent analytic package;
- mollifier architecture and channel-by-channel limits;
- literal-tent explicit formula;
- exact finite zero-side bridge;
- full real dictionary EF recovery by finite contraction.

### D0 representation layer

Closed classifications include:

- **D0-C:** cutoff-free finite source matrix theorem-locked;
- **D0-R:** generic R002 smooth-taper production object is **SPECIALIZATION_ONLY**, not identical to canonical CCM;
- **D0-B:** Bombieri's zero-index truncation is a different finite object; no direct deterministic Fourier-band identification was promoted.

### G0 localized finite-space layer

Closed:

- hard-window Fourier basis correlation;
- centered `Fin (2N+1)` basis wrapper;
- actual zero-extended finite additive vectors;
- arbitrary complex coefficient transport;
- exact finite autocorrelation/correlation normalization.

### G1-A internal additive restriction

Closed:

```text
localizedWeilAdditiveRHS(localizedFiniteVector u)
  = quadraticForm(cutoffFreeMatrix) u.
```

This is an internal additive explicit-formula statement, not the external CCM `QW_lambda` theorem.

### G1-B0 direct source finite matrix

Closed:

```text
sourceEq44Matrix = cutoffFreeMatrix.
```

The later printed normalization is non-load-bearing for the direct finite matrix.

### Source-normalization repair

Closed:

```text
canonicalSourceMatrix = sourceEq44Matrix = cutoffFreeMatrix = dictionaryMatrix.
```

The canonical displacement theorem and rank-at-most-two theorem are exported on `canonicalSourceMatrix`.

### G1-B1A finite source kappa / source-sector bridge

Closed in merged PR #72:

- `sourceLength lam = 2 * log lam` is positive for `lam > 1`;
- `u -> log(lam*u)` and `x -> lam^-1 * exp(x)` are theorem-locked inverse coordinates on the source-valid domains;
- interval transport `[lam^-1,lam] <-> [0,sourceLength lam]` is theorem-locked;
- source equation-(3.21) `V_n = kappa(U_n)` is preserved at formula level;
- arbitrary complex centered finite combinations transport with unchanged coefficients;
- `sourceFiniteVector` is the actual zero-extended source vector on `[lam^-1,lam]`;
- `sourceKappaFiniteVector_eq_sourceFiniteVector` is the production endpoint.

This closes only the finite coordinate/source-sector layer. It does not provide the multiplicative-Haar measure, bundled L2 isometry, `PsiSharp`, or ambient `QW_lambda` correspondence.

## Current gates from the validated post-W2-ZS state

### W2-A — genuine W / literature-RHS pair bridge

**CLOSED / PROVED / REGISTERED.**

Claim: `R003_WEIL_PAIR_LITERATURE_BRIDGE`.

For arbitrary complex-valued `f,g`, with `f` C² and compactly supported and `g` continuous and compactly supported, Lean proves pairwise Wsummand summability and

~~~text
zetaZeroConfig.W f g
  = EF.literatureRHS (EF.weilTest f g).
~~~

### W0 — one physical negative Weil test

**CLOSED / PROVED / REGISTERED.**

Claim: `R003_NEGATIVE_WEIL_TEST_CONTRACTION`.

Every concrete off-line zero yields one compact C² pole-neutral test with strict negative W self-value.

### W1 — strict finite-aperture recentering

**CLOSED / PROVED / REGISTERED.**

Claim: `R003_STRICT_APERTURE_NEGATIVE_WEIL_TEST`.

Every concrete off-line zero yields `L>0`, `r>0`, `L=4r` and a compact C² pole-neutral test with

~~~text
tsupport h ⊆ Ioo r (3*r)
tsupport h ⊆ Ioo 0 L
Re(W(h,h)) < 0.
~~~

### W2-ZS / direct diagonal W2-C endpoint

**CLOSED / PROVED / REGISTERED.**

Claim: `R003_WEIL_LOCALIZED_ADDITIVE_SELF_BRIDGE`.

For every compact C² concrete-zeta test:

~~~text
zetaZeroConfig.W h h
  = Zeta23.CCM.localizedWeilAdditiveRHS h h.
~~~

Production theorem:

~~~text
Zeta23.ExceptionalZero.zeta_W_self_eq_localizedWeilAdditiveRHS
~~~

Exact #83 theorem head:

~~~text
556be6c2b42e912c58751988c580ab4e0091822d
~~~

The proof closes ZS0-ZS6 on the summable concrete zero side and has axiom surface `[propext, Classical.choice, Quot.sound]`.

This proves the diagonal endpoint without proving the old analytic W2-B route.

### W1 + W2-ZS negative localized-additive witness

**CLOSED / PROVED / REGISTERED.**

Claim: `R003_STRICT_APERTURE_NEGATIVE_LOCALIZED_ADDITIVE_WITNESS`.

Lean preserves the full W1 aperture/margin/pole-neutrality package and replaces the strict negative W endpoint by

~~~text
Re(localizedWeilAdditiveRHS h h) < 0.
~~~

The strong theorem is

~~~text
Zeta23.ExceptionalZero.
exists_strictAperture_poleNeutral_negativeLocalizedWeilAdditiveRHS_of_offLine_zero
~~~

with minimal companion wrappers for F0-B/F1-roadmap composition.

### F0-B — finite approximation / strict-negativity transfer

**OPEN / PRIMARY INTERNAL FRONTIER.**

Goal: move the strict negative localized-additive witness into some finite centered sector consumed by G1-A.

Two candidates remain live.

#### F0-B1 — boundary-flat global C² approximation

Construct finite centered trigonometric polynomials whose endpoint value/first/second derivative vanish, so their zero extensions are global compact C² tests.

Coefficient moment constraints:

~~~text
sum u_n = 0
sum n*u_n = 0
sum n^2*u_n = 0.
~~~

If legal, #83 applies to every approximant:

~~~text
localizedWeilAdditiveRHS(p_N,p_N)=W(p_N,p_N).
~~~

Then prove `W(p_N,p_N) -> W(h,h)`.

#### F0-B2 — direct localized-additive continuity

Use the existing G0/G1-A legal finite vectors directly and prove

~~~text
localizedWeilAdditiveRHS(v_N,v_N)
  -> localizedWeilAdditiveRHS(h,h).
~~~

#### F0-B continuity firewall

Pointwise `Summable` for each approximant is not uniform family-level domination. Any dominated-convergence route must prove a uniform summable majorant or another quantitative continuity theorem.

The current canonical seed interface is C⁴ and the pole-killer interface consumes two derivatives to produce C². A C⁴ final witness would therefore naturally require at least C⁶ upstream seed regularity, but no such upgrade should be theoremized unless F0-B actually needs it.

The bounded decision rule is to choose the smaller theorem surface, not the more familiar approximation technology.

### Dormant analytic cross-check

The historical I0/I1/I2 -> W2-B -> analytic W2-C route remains OPEN / DORMANT. It should be revived only for independent cross-validation or if a later theorem needs the explicit pole/prime/gamma decomposition.

### G1-B1B — source Hilbert/functional bridge

**OPEN.**

Formalize only the minimum external analytic interface required for Proposition 3.2:

- multiplicative Haar measure `d*u = du/u` as needed;
- the relevant L2/isometry interface from Proposition 3.2(i);
- log transport of convolution/involution;
- the `PsiSharp` / evenization normalization;
- Proposition 3.2(ii):
  `QW(kappa f,kappa g) = PsiSharp(F)`,
  with the exact source definition of `F`.

### G1-final — actual finite source restriction

**OPEN.**

Compose G1-A + source normalization + G1-B1A/B1B to prove the independent source-functional theorem

```text
QW_lambda restricted to E_N
  = canonicalSourceMatrix.
```

Do not define `QW_lambda` to return the desired matrix.

## Downstream route after G1

### T22-canonical — high-frequency/adversarial falsifier

Before investing heavily in finite-to-infinite closure, stress the **canonical** source matrix and exact source restriction.

No legacy-`finiteMatrix` inertia/PSD evidence may be used as canonical spectral-sign evidence.

### G23 — source form-core / minimum-eigenvalue transfer

The older roadmap split this into G2 form-core density and G3 Rayleigh-bottom convergence.

The present research hypothesis is that the exact source proposition packaging both facts should be ported directly if its hypotheses match the now-formalized objects. This is a **LEAD**, not yet a project theorem.

Target mathematical content:

```text
E = span{V_n : n in Z} is a core for QW_lambda
and
minEig(QW_lambda|E_N) -> inf QW_lambda.
```

### S-NEG — fixed-aperture source negative-bottom lock

The independent source-negativity theorem must be pinned exactly before formalization:

```text
not RH
  -> exists fixed lambda > 1
     with inf QW_lambda < 0
```

or the exact source-equivalent statement actually available.

No source result may be upgraded beyond its literal hypotheses.

### Canonical finite obstruction

There are two distinct legitimate routes to F1. Their prerequisites must not be conflated.

**Primary internal additive route:**

~~~text
W0/W1 negative compact test                    [PROVED]
  -> W2-ZS direct W/localized identity          [PROVED]
  -> strict negative localized additive witness [PROVED]
  -> F0-B finite approximation/continuity       [OPEN]
  -> G1-A                                       [PROVED]
  -> F1 canonical finite obstruction            [OPEN].
~~~

**Dormant analytic cross-check:**

~~~text
I0/I1/I2 -> analytic W2-B/W2-C
           -> F0-B -> G1-A -> F1.
~~~

The endpoint is already proved by W2-ZS; this route is independent validation only.

**Source-faithful route:**

~~~text
SOURCE INTERFACE:
  G1-B1A [PROVED]
    -> S-IFACE / G1-B1B
    -> G1-final

SOURCE NEGATIVITY ENTRY:
  S-NEG
  or exact W/localized-additive/QW sign-carrying composition

COMMON:
  negative ambient QW + G1-final finite restriction
    -> G23
    -> F1 canonical finite obstruction.
~~~

OBS-015 forbids treating source interface closure as source negativity.

F1 would still not prove RH. A separate finite-negative exclusion theorem remains necessary.

## Dormant / composition tools

Potentially useful after canonical finite negativity becomes exact:

1. **D0-R — R002 map-or-separate: SETTLED BY PR #66.** The hard-window truncated-character geometry underlying `qBasis` is a real specialization-level connection, but no generic production theorem identifies the smooth-taper R002 `Gz/G-tilde(T)` family with the canonical CCM finite object. The exact R002 decomposition `Gz = Az + Ez`, the current `lambda <= 1` validity envelope, carrier shift, dynamic dimension, and taper dependence remain distinct. Therefore R002 masking stays on the R002 side and is no longer a CCM critical-path bottleneck.
2. **D0-B — Bombieri correspondence: SETTLED AS DISTINCT TRUNCATIONS.** The 2000 memoir truncates the zero-index multiset `Gamma_N={gamma: |gamma|<=N}` and studies `H(Gamma_N;t)`, whose dimension is `#Gamma_N`. The CCM object instead truncates a deterministic centered Fourier-character dictionary `-N,...,N`, of dimension `2*N+1`. No direct equality, congruence, compression, or parameter map is established, and Bombieri's inertia theorem is therefore not transferred to CCM. See `D0_B_BOMBIERI_CORRESPONDENCE_2026_08_30.md` and `../../external/bombieri/SOURCE_MAP.md`.
3. **G0-A — localized Fourier basis map: REACHED IN PR #68.** The normalized hard-window character correlation is compiler-proved to equal the existing `qBasis` formula on the centered Fourier indices, and the production factor-two firewall `2*dictionaryBasisTest = kernel` is theorem-locked. See `G0_LOCALIZED_BASIS_MAP_2026_08_30.md`.
4. **G0-B — actual finite localized space: REACHED IN PR #69.** The full complex centered `Fin (2*N+1)` sector is realized as actual zero-extended compactly supported L2 functions. Their inherited symmetrized `EF.weilTest` autocorrelation is globally exactly `2*dictionaryTest`, with no reality/evenness/zero-sum/positivity/RH restriction, and the zero-shift endpoint is exactly `2*coefficientMass`. See `G0_B_LOCALIZED_FINITE_SPACE_SETTLEMENT_2026_08_31.md`.
5. **G1-A — additive source-functional restriction firewall: REACHED IN PR #70.** The repository additive half-correlation RHS is compiler-proved, on every actual full-complex localized finite vector, to equal `quadraticForm (cutoffFreeMatrix L N) u`. The factor-half comes directly from #69's global `correlation = 2*dictionaryTest`; the proof then consumes the existing arbitrary-complex deterministic RHS theorem and `dictionaryMatrix = cutoffFreeMatrix`. A lambda wrapper theorem locks `L = 2*log(lambda)`. This is not yet promoted as the external CCM `QW_lambda` restriction.
6. **G1-B0 — Section-4 source-normalization firewall: REACHED IN PR #71.** After the post-green source reread, the direct equation-(4.4) diagonal was corrected: substituting the source formula `q(U_n,U_n)(y)=2(1-y/L)cos(2*pi*n*y/L)` gives the `(cos-exp(-x/2))*rho + w(L)` primitive, and Lean now proves the resulting source equation-(4.4) matrix is exactly the independently audited `cutoffFreeMatrix`. Separately, the printed equation-(4.11) rewrite is theorem-locked as suspect: its algebraically forced correction is `exp(x/2) * cCorrectionIntegrand`. The open proposition `SourceEq411CorrectionIdentity` now refers only to that printed rewrite; it is not used to justify the production matrix.
7. **G1-B1A — finite kappa coordinate/source-sector bridge: REACHED IN PR #72.** `sourceKappaFiniteVector_eq_sourceFiniteVector` theorem-locks the production endpoint for arbitrary complex centered coefficients; companion theorems lock `L=2*log(lambda)`, the logarithmic coordinate and inverse, interval transport, equation-(3.21) `V_n=kappa(U_n)`, source support, and finite-sector membership. The multiplicative-Haar L2 isometry from Proposition 3.2(i) is deliberately not inferred.
8. **G1-B1B — kappa/PsiSharp/QW source correspondence: ACTIVE PARALLEL SOURCE LANE.** Port the remaining source-facing analytic interface, beginning with any still-needed `d*u`/L2-isometry infrastructure from Proposition 3.2(i), then theorem-lock Proposition 3.2(ii): `QW(kappa f,kappa g)=PsiSharp(F)`, `F(u)=q(f,g)(log u)`, specialized first to the existing finite Fourier sector. Only this step earns the phrase "actual localized Weil-form restriction".
9. **G2/G3 source-port / finite-to-infinite layer: OPEN.** After the actual `QW_lambda` finite restriction is theorem-locked through G1-B1B, port the exact form-core/Rayleigh-bottom theorem needed by the fixed-aperture route rather than re-proving a larger spectral theory from scratch.
10. Revisit prolate/Jacobi structure only after the source restriction topology is theorem-locked. The old small-commutator-to-eigenvector route remains falsified by spectral-gap collapse.

Each must be re-audited against the canonical normalization before use in a spectral-sign argument.

## Dead or quarantined identifications

Do not silently revive:

- forbidden direct identification of `finiteMatrix` with `QW_lambda|E_N`;
- generic R002 smooth-taper `G-tilde(T)` = canonical CCM;
- Bombieri zero-index truncation = deterministic CCM Fourier truncation;
- fitted-small-commutator -> eigenvector convergence without an explicit generator and gap theorem.

See `../../DEAD_ROUTES.md`.

## Claim firewall

**PROVED on merged main through PR #84:** finite/dictionary/zero-side/cutoff-free matrix identities, G0 localized finite-space geometry, G1-A additive restriction, direct Section-4 matrix normalization, canonical source normalization, G1-B1A finite `kappa`/source-sector transport, canonical finite displacement, W2-A pairwise W/literatureRHS bridge with summability, W0 negative-test contraction, W1 strict finite-aperture recentering, W2-ZS concrete-zero-side evenization, the direct diagonal W/localized-additive identity, and the strict-aperture negative localized-additive witness.

**OPEN:** F0-B finite approximation/continuity, family-level W continuity/uniform zero-side domination, direct localized-additive continuity on the existing finite vectors, the old analytic W2-B route, multiplicative-Haar L2 interface, `PsiSharp`, ambient `QW_lambda`, actual source restriction theorem, S-NEG/sign composition, form-core/minimum-eigenvalue transfer, F1, first-crossing reduction, K0-K3 finite-wall exclusion, finite-negative exclusion, RH.

## Next-move rule

The semantic work-package names are authoritative. Historical PR numbers are execution history only and must not be used as stable roadmap identifiers.

Whenever one gate goes green, perform the post-green research pass before selecting the next gate.

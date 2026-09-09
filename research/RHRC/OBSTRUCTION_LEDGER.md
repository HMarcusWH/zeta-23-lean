# RHRC obstruction ledger

This ledger records reusable blockers that should shape future route design.

> **Current theorem anchor:** merged PR #134, `7f1fec480d1ccbff04a456ab937accf7b23cc1af`.  
> **Validated theorem head:** `753ee53a7fc08bd3be9a5a0f37417629122395f9`.  
> **Validated theorem tree:** `c142efa141036331d139c532d06e7a976c5b50c2`.  
> **Claim firewall:** RH remains OPEN.

## OBS-001 — TightMult information wall

**Status:** FORMAL / UNCONDITIONAL.

At `c=2`, the inherited Zeta23 certificate based on trace, Frobenius norm, on-line multiplicity atoms and a positive-index bound is simultaneously extremal for an on-line double zero and a tight off-line pair.

**Escape requirement:** introduce a genuinely new information channel.

## OBS-002 — density-one is not RH

Any method insensitive to `o(N)` exceptional zeros cannot close RH.

## OBS-003 — conditional support > 1

Routes requiring conjectural prime-pair / pair-correlation input remain conditional until that ancestry is independently discharged.

## OBS-004 — pointwise cancellation hazard

A single exponentially growing summand does not imply growth of the magnitude of the total residual. Cancellation must be controlled.

## OBS-005 — FFBBP target leakage

RUN_36 used target-dependent cost in association. Permanent regression fixture.

## OBS-006 — FFBBP source-side false-field bias

RUN_37 removed target leakage but still produced a field in a known-null world. Unknown-field discovery requires known-null suppression and matched controls.

## OBS-007 — window artifact

RUN_41 `curvature_gap` lost to a matched W96 adversarial null and failed the predeclared transfer condition.

## OBS-008 — scalar prime-upper equivalence wall

**Status:** FORMAL / UNCONDITIONAL (Lean).

The R001 scalar target `ArithmeticSideSubexponential` is logically equivalent to RH.

**Consequence:** closing that scalar arithmetic leg in the same observable class is proving RH, not obtaining a cheap auxiliary estimate.

## OBS-009 — band-limited Weil-positivity wall

**Status:** classical design constraint; not fully formalized as a project theorem.

The R002 negative-index arithmetic leg is a band-limited Weil-positivity assertion. Requiring the whole relevant family restores RH-strength positivity.

## OBS-010 — finite formula identity is not an ambient restriction theorem

**Status:** PROJECT FIREWALL.

A theorem

```text
finite source formula = matrix M
```

does not by itself prove

```text
QW_lambda restricted to E_N = M.
```

The latter additionally requires the correct carrier/function space, measure, source functional, normalization and restriction map.

**Origin:** repeated R003 source/normalization audits culminating in #71/#73.

## OBS-011 — scalar-normalization spectral-sign firewall

**Status:** FORMAL STRUCTURAL CONSEQUENCE.

If `A=M+cI`, commutators, eigenvectors/eigenspaces and eigenvalue gaps transport, but absolute eigenvalues and sign-sensitive quantities shift.

Therefore legacy `finiteMatrix` numerical inertia/PSD/lower-bound evidence cannot be promoted to canonical source spectral evidence.

## OBS-012 — function-level E_N is not bundled L2/form-domain E_N

**Status:** PROJECT FIREWALL.

A formula-level or zero-extended function representing the finite source Fourier span is not automatically an element/subspace of the exact `L2(d*u)` or form domain used by an external source theorem.

## OBS-013 — source-display reconciliation is a theorem obligation

**Status:** PROJECT FIREWALL.

Different source displays can encode distinct normalizations. Agreement with one source formula, executable or numerical oracle does not authorize relabeling another display.

**Origin:** direct equation-(4.4) versus later printed equation-(4.11)/(4.14) CCM normalization seam.

## OBS-014 — PR numbers are not mathematical dependencies

**Status:** DOCUMENTATION / GOVERNANCE.

Roadmaps repeatedly diverged from predicted PR numbering as proof results compressed or split dependencies.

**Consequence:** stable route documentation should use semantic work-package IDs; PR numbers are execution history.

## OBS-015 — source interface is not source negativity

**Status:** PROJECT FIREWALL.

A theorem defining or identifying the source functional does not by itself transport the project theorem `Re W(h,h)<0` into a strict negative value of an independently defined source `QW`.

**Escape requirement:** separately prove source negativity or an exact sign-preserving composition theorem.

## OBS-016 — raw periodic approximation is not hard-window legality

**Status:** PROJECT FIREWALL; PRIMARY R003 ESCAPE PROVED.

PR #91 proves uniform formula-level approximation by periodic finite localized Fourier functions on one fixed aperture, but not global hard-window `C²` legality for the raw zero extension. PR #93 closes the primary route with `exists_boundaryFlatFinite_WCONT_approx`.

**Permanent warning:** do not infer legality for unrelated raw periodic approximants or for the correction vector alone.

## OBS-017 — raw function-space norm is not Euclidean Rayleigh normalization

**Status:** PROJECT FIREWALL; PRIMARY ESCAPE CLOSED BY PR #107.

PR #98 closes the Euclidean carrier/quadratic bridge, #100 closes exact Euclidean N-flow, and #107 proves orthogonal parity compression, compressed/self agreement, symmetry and a negative constrained Rayleigh eigenmode.

**Permanent warning:** #100 isometry does not imply full compressed-operator intertwining; #110 proves only a rank-at-most-one parity defect.

## OBS-018 — merged source presence is not compiler validation

**Status:** PROJECT VALIDATION FIREWALL.

A `.lean` file existing, appearing in a PR, passing syntactic no-placeholder checks or being merged does not establish that its declarations elaborate.

**Origin:** PR #103 merged `ParityBadness.lean` without putting it in the validated `Zeta23.CCM` import/build closure; #105 later closed that gap.

**Permanent rule:** theorem validity requires exact compiler-tested closure. Machine claim promotion is a separate surface and may require explicit binding/axiom checks.

## OBS-019 — one-dimensional successor shell is not an invariant negative line

**Status:** PROJECT FIREWALL; BLOCK-GEOMETRY ESCAPE CLOSED BY #112/#113; CANONICAL COORDINATE CLOSED BY #118; SPECIAL ZERO-SHIFT SHELL RESPONSE CLOSED BY #127.

Now PROVED:

```text
V = W ⊕ S
dim_C S = 1
intrinsicShellPart(v_bad) != 0
intrinsicShellPart(x)=0 <-> x in W
canonical cubic shell vector c != 0
canonical shell coordinate reconstructs every s in S
canonical quotient coordinate vanishes exactly on W
for the decoupled zero-shift trial u0:
  T u0 = shellPart(T u0)
  sigma0*c = T u0
  S0 = star(sigma0)<c,c>.
```

Still not proved:

- the negative eigenmode is purely shell;
- the shell is invariant under the compressed canonical operator;
- `u0` is an eigenvector;
- D transports the shell orthogonally;
- negative index exactly one / unique negative eigenline as a separately formalized theorem.

**Consequence:** the old “theoremize shell response” escape is consumed. Future arguments may use the exact special response, but must not silently upgrade it to invariant-subspace spectral theory.

## OBS-020 — exact one-channel parity factorization is not unitary rank-one perturbation theory

**Status:** PROJECT FIREWALL; FACTORIZATION CLOSED BY #112; QUOTIENT VISIBILITY CLOSED BY #118; SOURCE-EXPLICIT DEFECT CLOSED BY #129; SOURCE DECOMPOSITION CLOSED BY #131; DENOMINATOR-FREE ZERO-SHIFT SOURCE TRANSPORT CLOSED BY #134; METRIC/UNITARY TRANSFER THROUGH D STILL UNPROVED AND UNNEEDED FOR THE CURRENT ROUTE.

#110/#112 prove algebraic one-channel / rank-at-most-one parity defect structure and exact pointwise cubic factorization. #118 identifies the odd cubic defect coefficient with the canonical quotient coordinate. #129 proves the coefficient is exactly the canonical-source quadratic normal moment. #131 proves the production pole/arch/prime decomposition. #134 proves the exact whole-kernel zero-shift transport without upgrading D metrically.

Still not proved:

- useful sign or nonzeroness of the canonically composed source/overlap quantity;
- exact defect rank one rather than rank zero-or-one;
- D is unitary/isometric;
- conjugated odd compression is self-adjoint in the original even-sector metric;
- Hermitian rank-one interlacing, equal spectra or inertia transfer through D.

**Current escape route:** spend actual canonical source normalization through absolute energy/coercivity. Do not import metric perturbation theory through D.

## OBS-021 — shifted Schur identity is not an exact secular criterion

**Status:** HISTORICAL BLOCKER CLOSED BY PR #119; PERMANENT GENERIC-SCHUR WARNING REMAINS.

PR #119 proves

```text
cubicSecularScalar(lam)=0
  <-> full residual = 0
  <-> exists nonzero eigenmode at lam.
```

**Permanent warning:** exact secular equivalence is still not a contradiction. Generic Hermitian block systems can have negative secular roots.

## OBS-022 — quotient secular scalar versus explicit Schur scalar

**Status:** HISTORICAL BLOCKER CLOSED BY PR #121/#122; PERMANENT REPRESENTATION WARNING REMAINS.

PR #121 identifies the quotient scalar with the conjugated explicit Schur scalar; #122 proves the symmetry/realness needed for

```text
F(lam)=S(lam)/<c,c>
```

on the safe negative-shift regime.

**Permanent warning:** the identity is theorem-backed only under its stated hypotheses. Do not treat the two definitions as globally definitionally identical.

## OBS-023 — predecessor nonnegativity permits zero resonance

**Status:** CURRENT STRUCTURAL OBSTRUCTION; CLASSIFICATION/POLE INFRASTRUCTURE CLOSED THROUGH #128; EXACT ZERO-SHIFT KERNEL/SOURCE COMPATIBILITY CLOSED BY #134; SOURCE-SPECIFIC RESONANT EXCLUSION OPEN.

Global-first-bad gives `Re <Aw,w> >= 0`, not a positive lower spectral gap. Thus `ker A` may be nontrivial.

The theorem chain now gives:

```text
#122: Az=0 -> (<z,b>=0 <-> Tz=0)
#124: W=ker A⊕range A; exact resonant identity/bound
#125: canonical regular endpoint with Re S0<0
#127: exact special shell response
#128: canonical kernel coordinate K;
      k=K(b)=0 in the decoupled branch;
      k!=0 in the resonant branch;
      (-lam)K(R_lam b)=k.
#129: exact cross-parity source transfer
#131: exact pole/arch/prime source-moment decomposition
#134: A-(Dz)=beta(z)d+mu(z)a;
      whole odd-kernel vector compatibility;
      direct zero-shift transfer;
      Gamma0*mu(z)=0 on every z in ker A+ under both preimage hypotheses.
```

The surviving obligation is now source-specific and sign-sensitive: prove an absolute canonical energy/coercivity theorem strong enough to force the coupling to annihilate `ker A` or otherwise make the resonant first-bad state impossible.

**Semantic firewall:** `ker A` is the kernel of the projected successor predecessor block. It is not identified with the kernel of the predecessor-size compressed operator.

## OBS-024 — root uniqueness is not root exclusion

**Status:** PERMANENT CLAIM FIREWALL.

The exact root detector has a real explicit scalar representation, so strict monotonicity/root-count control is a legitimate theorem target. Even if E3-C proves at most one negative root, a single negative root may still exist — and a hypothetical off-line zero already forces one.

`at most one negative root` must never be documented as positivity or RH.

## OBS-025 — negative zero-shift endpoint / signed shell response is not a contradiction

**Status:** CURRENT PROJECT FIREWALL; EXPOSED BY #125 AND SHARPENED BY #127/#128/#134.

The decoupled global-first-bad branch has

```text
Re S0 < 0
S0 = star(sigma0)<c,c>
Re sigma0 < 0.
```

#134 now gives exact direct zero-shift cross-parity transport around this endpoint, but generic Hermitian block systems with a nonnegative predecessor block can still have a negative zero-shift Schur complement and negative shell response. Therefore

```text
Re S0<0
Re sigma0<0
exact zero-shift transfer
  != regular-branch exclusion
  != negative-root exclusion
  != positivity
  != RH.
```

**Escape requirement:** use absolute canonical source information absent from the generic countermodels, preferably through source energy/one-step domination.

## OBS-026 — generic first-bad structural package is insufficient; actual canonical source values must do work

**Status:** EXPERIMENTALLY FALSIFIED GENERIC ROUTE / CURRENT DESIGN FIREWALL.

Post-#128 discovery countermodels show that increasingly rich generic structure can coexist with bad finite states:

- nonnegative predecessors with a negative regular Schur endpoint;
- exact zero resonance with a negative eigenvalue;
- actual centered-grid boundary-flat parity spaces with generic reversal-symmetric diagonal operators producing both-parity regular negativity, one-parity badness, or genuine resonance;
- reversal-symmetric diagonal perturbations preserving the displacement identity while altering the sign-sensitive successor state.

These fixtures are **EXPERIMENTAL SIGNAL**, not Lean theorems, realizable zeta configurations or counterexamples to `canonicalSourceMatrix`.

**Consequence:** a proposed contradiction based only on Hermitianity, first-bad minimality, parity, KKT, rank-at-most-one defect, shell response, resonance classification, displacement structure, or #134's transfer identities is not credible unless it identifies an additional invariant the fixtures do not preserve.

**Current escape requirement:** use the #131 pole/arch/prime source formula through an observable that retains the actual canonical normalization.

## OBS-027 — the #131 raw source moment is linear, so universal one-sided sign is unavailable

**Status:** DERIVED STRUCTURAL FIREWALL FROM PROVED #131 INTERFACE.

The production quantity

```text
explicitCanonicalSourceMoment L K v
```

is linear in the trial vector `v`.

Therefore

```text
explicitCanonicalSourceMoment L K (-v)
  = - explicitCanonicalSourceMoment L K v
```

and scalar/phase covariance must be respected.

**Consequence:** unless the functional is identically zero, no theorem asserting universal strict positivity or universal nonnegativity of the raw moment on the whole even boundary-flat vector space can be true.

This does **not** exclude sign/nonzero/phase control on a canonically oriented state after composing with additional arithmetic/branch data.

## OBS-028 — factorwise cross-parity nonvanishing/sign is not structural

**Status:** EXPERIMENTALLY FALSIFIED GENERIC ROUTE / EXACT RATIONAL REGRESSION FIREWALL.

Exact rational centered-grid reversal-symmetric diagonal models retain the actual legal parity/boundary-flat spaces, predecessor nonnegativity, KKT extraction, rank-one cubic defect, quotient transport, shifted trial reconstruction, overlap formula and full #129 transfer while realizing:

```text
sourceMoment(u+) != 0 but Gamma = 0 at a common negative root
Gamma != 0 but sourceMoment(u+) = 0 at a common negative root
alpha = 0 at an odd-only negative root while the even successor is positive
```

Additional exact fixtures realize negative `Gamma`, negative `alpha`, and either sign of the source moment.

These fixtures are not the canonical arithmetic source and do not refute a future source-specific theorem.

**Consequence:** no argument may divide by `alpha`, `Gamma`, overlap, source moment, `Gamma0`, or `mu(z)` without a separate theorem proving the required nonzeroness from canonical source information. #134's product law does not change this.

**Escape requirement:** use an exact canonical pole/arch/prime normalization theorem that visibly fails on the generic fixtures.

## OBS-029 — scalar-shift-invariant transfer data cannot locate the absolute spectral origin

**Status:** DERIVED STRUCTURAL FIREWALL / EXACT RATIONAL CHECK.

In the generic first-bad transfer package, the simultaneous shift

```text
M -> M+tI
lambda -> lambda+t
```

can leave shifted resolvent equations, trial vectors, cubic defect/source functional, `alpha`, `Gamma`, and secular transfer data unchanged while moving the spectrum relative to zero.

**Consequence:** no terminal negative-root contradiction can come from the shift-invariant structural package alone. The proof must spend an information channel that remembers the actual canonical scalar normalization.

The #131 quadratic-normal moment deliberately annihilates scalar identities, so another decomposition of the same observable cannot recover that missing information.

**Escape requirement:** restore the absolute canonical source energy / one-step block normalization, including the archimedean scalar correction.

## OBS-030 — one-step domination is the unresolved arithmetic content

**Status:** CURRENT DECISIVE OPEN OBSTRUCTION.

For either parity, let

```text
A = P_W T|_W
c = canonical shell vector
b = P_W T c
q_c = Re<Tc,c>.
```

With `A>=0`, the target

```text
q_c >= 0
|<w,b>|^2 <= q_c Re<Aw,w>  for every w in W
```

is equivalent to positivity of the one-step block extension.

This target is not supplied by first-bad minimality, Hermitianity, parity, KKT, the rank-one defect, cross-parity transfer, #134's zero-shift transport, or factorwise source information. Exact rational fixtures with strictly positive predecessor blocks still admit negative successor roots.

If the domination theorem is derived from the actual canonical source, then

```text
w in ker A -> <w,b>=0
```

so the coupling lies in `range A` and resonance disappears. In the regular branch, choosing `Ax0=b` gives `S0>=0`, contradicting the already-proved `Re S0<0` at the forced negative root.

**Current escape route:**

1. #134 denominator-free zero-shift kernel/source transport — **CLOSED / PROVED**;
2. theoremize an absolute pole/arch/prime source-energy decomposition retaining the scalar correction — **NEXT**;
3. prove the canonical one-step domination/coercivity estimate in both parities — **DECISIVE**;
4. use high-order source-coordinate cancellation or log-lift regular-aperture selection only if they materially support step 3.

## OBS-031 — exact zero-shift transport is not factorwise or branch exclusion

**Status:** FORMAL POST-#134 CLAIM FIREWALL.

PR #134 proves, under both zero-shift preimage hypotheses,

```text
sigma- = alpha0 sigma+ + Gamma0*mu(u+0)
Gamma0*mu(z)=0  for every z in ker A+.
```

It also proves the whole-kernel vector transport before any regularity assumption.

These statements constrain the admissible counterexample space but do not imply:

```text
Gamma0 != 0
mu(z) = 0
Gamma0 = 0
source sign
branch exclusion
negative-root exclusion
RH.
```

**Consequence:** #134 consumes the zero-shift transport bottleneck. Future work must not keep repackaging the same product/transport identities as if they were new closure information. The next route must spend the absolute canonical normalization.

**RH remains OPEN.**

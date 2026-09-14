# RHRC obstruction ledger

This ledger records reusable blockers that should shape future route design.

> **Current theorem anchor:** merged PR #163, `bd3fa1aafa7df2aa35873df532bdb6f17ddd2bbd`.  
> **Validated theorem head:** `b418ff034428f92594bab0e5b8276181a086ee4b`.  
> **Validated theorem tree:** `c397b3a015ea54e38ecfe626d6e29556fe963839`.  
> **Latest research-evidence anchor:** merged PR #168, validated head `9657dad6f1e262b1fa7e08e6944aaa935feeaf33`.  
> **Claim firewall:** RH remains OPEN.

Historical obstruction origins below retain the PR number at which they were discovered/classified. A later theorem may close an escape without deleting the reusable warning.

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

**Status:** PROJECT FIREWALL; FACTORIZATION CLOSED BY #112; QUOTIENT VISIBILITY CLOSED BY #118; SOURCE-EXPLICIT DEFECT CLOSED BY #129; SOURCE DECOMPOSITION CLOSED BY #131; ZERO-SHIFT SOURCE TRANSPORT CLOSED BY #134; ABSOLUTE ENERGY CLOSED BY #136; SOURCE PAIRING/ONE-STEP DETERMINANT CLOSED BY #137; SOURCE-COORDINATE D TRANSPORT CLOSED BY #157; SAME-STATE CROSS-PARITY SOURCE COMPOSITION CLOSED BY #161; METRIC/UNITARY TRANSFER THROUGH D STILL UNPROVED AND UNNEEDED FOR THE CURRENT ROUTE.

The project now has exact algebraic defect/source transport, scalar-sensitive self-energy, complex source pairing, the denominator-free one-step determinant, theorem-backed source-coordinate derivative transport, and a retained same-state cross-parity source obstruction. None of these upgrades D to an isometry or transports Hermitian perturbation theory through D.

Still not proved:

- useful sign of the full canonical one-step determinant;
- exact defect rank one rather than rank zero-or-one;
- D is unitary/isometric;
- conjugated odd compression is self-adjoint in the original even-sector metric;
- Hermitian rank-one interlacing, equal spectra or inertia transfer through D.

**Current escape route:** spend actual canonical source normalization through the theorem-backed transformed/source-moment machinery. Do not import metric perturbation theory through D.

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

**Status:** STRUCTURAL OBSTRUCTION; CLASSIFICATION CLOSED THROUGH #128; ZERO-SHIFT SOURCE COMPATIBILITY CLOSED BY #134; CONDITIONAL RESONANCE REMOVAL CLOSED BY #137; SELECTED RESONANCE REMOVED BY #150; ARBITRARY-PARITY PREDECESSOR NONNEGATIVITY INTERFACE CLOSED BY #161; CANONICAL SIGN THEOREM OPEN.

Global-first-bad gives `Re <Aw,w> >= 0`, not a positive lower spectral gap. Thus a generic first-bad predecessor may have nontrivial kernel.

For the current selected #150/#153 state, resonance is removed directly. #161 additionally exposes whole-cell predecessor nonnegativity for either parity, which is enough for the current shifted cross-parity composition without adding simultaneous zero-shift regularity.

**Semantic firewall:** `ker A` is the kernel of the projected successor predecessor block. It is not identified with the kernel of the predecessor-size compressed operator.

## OBS-024 — root uniqueness is not root exclusion

**Status:** PERMANENT CLAIM FIREWALL.

Strict monotonicity/root-count control may give at most one negative root. A hypothetical off-line zero already forces one. Root uniqueness remains weaker than root absence.

## OBS-025 — negative zero-shift endpoint / signed shell response is not a contradiction by itself

**Status:** PROJECT FIREWALL; EXPOSED BY #125, SHARPENED BY #127/#128/#134, REGULAR NEGATIVE CERTIFICATE CLOSED BY #150/#153, TRANSFORMED NEGATIVE CERTIFICATE CLOSED BY #157; BOUNDARY DEFECT EXPOSED BY #159; SAME-STATE SHIFTED RIESZ/SOURCE OBSTRUCTION CLOSED BY #161; MIXED-JET/RIESZ COUPLING CLOSED BY #163; OPPOSING RESTRICTION OPEN.

The retained selected state can carry

```text
lam < 0
explicit Schur root = 0
A x0 = b
canonicalSourceChannelEnergy(c-x0) < 0
canonicalRieszSourceChannelEnergy(...,6,...) < 0
exact signed Riesz boundary decomposition
same shifted even trial with R8 < 0 and exact R9/M4 boundary inequality
same shifted even trial with odd secular scalar = Gamma * explicit source moment
same shifted even trial with h^(7)(0) = -2*(2*pi)^6*M4
same shifted even trial with exact R8-R9 = endpoint scalar * squared mixed jet.
```

Therefore retained exact negative energy, its boundary decomposition, the #161 same-state source obstruction and the #163 mixed-jet coupling are not themselves a contradiction, negative-root exclusion, or RH.

## OBS-026 — generic first-bad structural package is insufficient; actual canonical source values must do work

**Status:** EXPERIMENTALLY FALSIFIED GENERIC ROUTE / CURRENT DESIGN FIREWALL.

Post-#128 discovery countermodels show increasingly rich generic structure can coexist with bad finite states. They are experimental/synthetic fixtures, not canonical source or zeta counterexamples.

**Post-#163 consequence:** a proposed contradiction based only on Hermitianity, first-bad minimality, parity, KKT, shell response, regularity, displacement structure, generic cross-parity transfer, generic smoothing/transport, or the structural existence of a mixed source jet is still not credible. The current proof must spend exact canonical arithmetic on the theorem-backed same-state source/mixed-jet/Riesz interfaces.

## OBS-027 — the #131 raw source moment is linear, so universal one-sided sign is unavailable

**Status:** DERIVED STRUCTURAL FIREWALL FROM PROVED #131 INTERFACE.

`explicitCanonicalSourceMoment L K v` is linear in `v`, hence negation/scalar covariance blocks universal one-sided sign on the whole vector space unless the functional vanishes identically.

**Consequence:** the later energy/Riesz route is quadratic/Hermitian and is not a revival of raw source-moment positivity.

## OBS-028 — factorwise cross-parity nonvanishing/sign is not structural

**Status:** EXPERIMENTALLY FALSIFIED GENERIC ROUTE / EXACT RATIONAL REGRESSION FIREWALL; SCOPED SAME-STATE NONVANISHING AVAILABLE THROUGH #161/#163.

Exact rational centered-grid reversal-symmetric diagonal models realize `Gamma=0`, source moment zero/nonzero, `alpha=0`, negative coefficients and both source-moment signs while preserving the generic transfer package.

#161 proves a scoped product-nonzero consequence only after adding the retained even-root state and opposite-parity goodness: the odd secular scalar is nonzero and equals `Gamma * explicitCanonicalSourceMoment`. #163 separately theoremizes `crossParityGamma_ne_zero_of_even_of_not_oddBad` on that same scoped branch.

**Consequence:** no argument may divide by `alpha`, `Gamma`, overlap, source moment, `Gamma0`, or `mu(z)` outside a theorem-backed nonzero scope.

## OBS-029 — scalar-shift-invariant transfer data cannot locate the absolute spectral origin

**Status:** DERIVED STRUCTURAL FIREWALL; ABSOLUTE-ENERGY ESCAPE CLOSED BY #136, PAIRING/DETERMINANT INTERFACE CLOSED BY #137, SELECTED NEGATIVE ENERGY CLOSED BY #150/#153, TRANSFORMED NEGATIVE STATE CLOSED BY #157, BOUNDARY STRUCTURE CLOSED BY #159, SAME-STATE TRANSFER CLOSED BY #161, MIXED-JET BOUNDARY INTERFACE CLOSED BY #163, OPPOSING RESTRICTION OPEN.

Under simultaneous generic scalar shift `M -> M+tI`, `lambda -> lambda+t`, the old shifted transfer package can remain unchanged while the spectrum moves relative to zero.

#161 places absolute negative Riesz/source energy and cross-parity source transfer on the same canonical shifted state. #163 additionally places the exact quadratic-normal mixed jet and squared-jet Riesz boundary on that state. The remaining question is an independent canonical arithmetic restriction incompatible with it.

## OBS-030 — one-step domination is an exact certificate; its arithmetic truth remains open

**Status:** FORMAL CERTIFICATE / DECISIVE UNIVERSAL SIGN CONTENT OPEN.

PR #137 defines `canonicalOneStepDomination` and proves its sufficiency for the desired zero-shift sign / negative-root exclusion mechanism.

The missing mathematics is not sufficiency. It is canonical arithmetic truth. Under predecessor nonnegativity and a one-dimensional shell, simply restating successor positivity has no research information gain.

## OBS-031 — exact zero-shift transport is not factorwise or branch exclusion

**Status:** FORMAL POST-#134 CLAIM FIREWALL; UNCHANGED BY #163.

PR #134 proves direct zero-shift transfer and `Gamma0*mu(z)=0` under both preimage hypotheses. Later determinant/regularity/certificate/discrepancy/Riesz, shifted #161 and mixed-jet #163 results do not license factorwise conclusions from that separate zero-shift product law.

## OBS-032 — determinant reduction can become a tautological positivity restatement

**Status:** POST-#137 RESEARCH-GAIN FIREWALL; UNCHANGED BY #163.

With `A>=0` and a one-dimensional shell, the universal determinant conditions encode essentially the missing positivity of the one-step block extension. A proof that merely assumes successor PSD, assumes absence of the negative root, or rewrites the same block positivity under a new name is circular.

**Escape requirement:** identify a canonical arithmetic mechanism implied by premises available before the desired conclusion.

## OBS-033 — the global/selected sign-failure countercertificate is not a contradiction

**Status:** FORMAL CLAIM FIREWALL; RETAINED/SHARPENED THROUGH #153, RIESZ-TRANSFORMED BY #157, BOUNDARY-RESOLVED BY #159, SAME-STATE SOURCE/RIESZ-COMPOSED BY #161, MIXED-JET/RIESZ-COMPOSED BY #163.

PR #137 first exposed global sign failure alternatives. PR #150 selects a regular negative-energy state. PR #153 retains its complete ancestry and exact negative source-channel state. PR #155 supplies the legal generic Riesz engine. PR #157 supplies exact production Riesz order 6 / even order 8 and strict retained transformed negativity. PR #159 exposes the exact first surviving moment-square boundary terms. PR #161 reconstructs the retained even negative root as the canonical shifted secular state and composes its Riesz obstruction with the exact cross-parity arithmetic source obstruction. PR #163 identifies the exact quadratic-normal mixed source jet, shows the finite-prime source term samples the same observable, and rewrites the retained R8-R9 boundary through the squared seventh jet.

**Consequence:** RH remains OPEN until new mathematics proves an incompatible canonical restriction on the exact forced state and the terminal RH wrapper is validated.

## OBS-034 — theorem-backed pole-prime cancellation must not be discarded silently

**Status:** FORMAL INTERFACE / POST-#153 RESEARCH-DESIGN FIREWALL; STRENGTHENED BY #155/#157/#159/#161/#163.

PR #153 proves

```text
matrixRealEnergy_pole_sub_prime_eq_discrepancy
canonicalSourceChannelEnergy_eq_discrepancy.
```

PR #155 proves a legal conditional Riesz representation without differentiating the prime staircase. PR #157 instantiates exact production Riesz-6/even-Riesz-8. PR #159 proves the signed boundary recurrence without dropping the archimedean/scalar terms. PR #161 composes the transformed state with `explicitCanonicalSourceMoment`, whose pole/arch/prime decomposition is exact. PR #163 further exposes the finite-prime source contribution as samples of the same analytic `quadraticNormalSourceAtom` whose local seventh jet controls the Riesz boundary.

**Consequence:** a proposed proof that returns to independent coarse pole and prime majorants, or replaces the exact transformed/source-moment cancellation by unrelated loose envelopes, must prove the loss harmless at the selected-residual scale.

## OBS-035 — endpoint-jet obligations must match the exact theoremized order

**Status:** POST-#155 CLAIM / ROADMAP FIREWALL; R6/R8 ESCAPE CLOSED BY #157; LEADING SELF-ENERGY COEFFICIENTS CLOSED BY #159; MIXED QUADRATIC-NORMAL SEVENTH-JET ESCAPE CLOSED BY #163; PERMANENT ORDER/SURFACE WARNING REMAINS.

PR #155 proves production source-coordinate oddness and all even endpoint derivatives vanish. PR #157 closes the missing odd cancellations needed for exact production Riesz order 6/even order 8.

PR #159 separately theoremizes

```text
g^(7)(0) = -2*(2*pi)^6*normSq(M3)
g^(9)(0) =  2*(2*pi)^8*normSq(M4)
```

for the exact self-energy scopes stated by the theorem declarations, and proves a general moment-prefix odd-jet law.

PR #163 independently theoremizes the different mixed observable

```text
h_v^(7)(0) = -2*(2*pi)^6*M4(v).
```

**Permanent warning:** do not transport derivative formulas between self-energy and mixed-pairing surfaces by type or analogy. Each derivative identity requires its own theorem-backed transport and normalization.

## OBS-036 — real contraction derivative transport is not complex production source-energy transport

**Status:** POST-#155 IMPLEMENTATION / CLAIM FIREWALL; EXACT SOURCE-ENERGY ESCAPE CLOSED BY #157; PERMANENT WARNING REMAINS.

A theorem only for a real contraction API does **not** by itself establish a theorem for arbitrary complex production trials.

PR #157 closes the exact required escape for `sourceAtomRealEnergy` by explicit real/imaginary decomposition and zero-sum defect cancellation. The resulting production transport is theorem authority.

**Permanent warning:** future real-vector helper theorems still require an explicit complex-production bridge before use on sesquilinear production energies.

## OBS-037 — self-energy moment jets are not mixed quadratic-normal source jets

**Status:** POST-#159 CLAIM / IMPLEMENTATION FIREWALL; ESCAPE CLOSED BY #163; PERMANENT SURFACE WARNING REMAINS.

PR #159 proves odd endpoint jets for

```text
sourceAtomRealEnergy K x
```

which is a real quadratic self-energy. #161 places a different, global complex linear source observable on the same retained shifted negative state through `explicitCanonicalSourceMoment`.

The local mixed observable is

```text
<centeredQuadraticNormal, sourceMatrix(omega) v>
  / <centeredQuadraticNormal, centeredQuadraticNormal>.
```

#163 closes the escape by theoremizing the mixed pairing directly, including all conjugation/normalization factors, and proving its seventh derivative proportional to `M4(v)`.

**Permanent warning:** the #163 result does not retroactively make the mixed jet a corollary of #159. Future cross-surface reuse still requires explicit bridge theorems.

## OBS-038 — nonzero explicit source moment does not imply nonzero M4

**Status:** POST-#161 STRUCTURAL / CLAIM FIREWALL; SHARED-OBSERVABLE INTERFACE THEOREMIZED BY #163; IMPLICATION STILL OPEN.

PR #161 proves, in the retained even-selected / odd-good branch,

```text
explicitCanonicalSourceMoment L (Nstar+1) evenShiftedTrial != 0.
```

This is a global canonical arithmetic linear functional containing pole, reduced archimedean diagonal/off-diagonal and finite prime-source contributions.

It does **not** imply

```text
centeredMoment (Nstar+1) 4 evenShiftedTrial != 0.
```

Conversely, nonzero `M4` does not by itself imply a nonzero explicit canonical source moment. Generic cancellation and scaling already make these different observables.

PR #163 strengthens the interface: the finite-prime contribution to `explicitCanonicalSourceMoment` is now theoremized as a weighted sum of values of the same `quadraticNormalSourceAtom` whose seventh jet is exactly proportional to `M4`. This does not close the implication because a finite weighted sample sum does not generically determine a local derivative, and pole/archimedean terms can also cancel.

**Escape requirement:** prove an additional canonical sampling/interpolation/cancellation relation on the exact retained state. The shared observable is now theorem authority; the global-to-local rigidity is not.

## OBS-039 — simultaneous parity badness remains an allowed branch

**Status:** POST-#161 OPEN-BRANCH FIREWALL; UNCHANGED BY #163.

The headline #161 theorem is a disjunction:

```text
odd successor bad
OR
explicit source moment != 0
```

under selected even first-bad parity. The left branch is not contradictory merely because even is already bad. #163 adds local mixed-jet/Riesz information on the retained even state but does not exclude odd badness.

**Escape requirement:** first falsify exact generic/rank-one models to determine whether simultaneous even+odd badness is structurally easy. Any surviving exclusion theorem must spend additional canonical arithmetic rather than assuming interlacing or metric equivalence through `D`.

## OBS-040 — a squared mixed-jet Riesz boundary identity is not an arithmetic sign theorem

**Status:** FORMAL POST-#163 CLAIM FIREWALL.

PR #163 proves

```text
2*(2*pi)^4*(R8-R9)
  = canonicalPolePrimeRieszEndpointScalar(L,8) * |h^(7)(0)|^2.
```

The norm square is nonnegative, but #163 proves neither

```text
canonicalPolePrimeRieszEndpointScalar L 8 >= 0
```

nor

```text
canonicalPolePrimeRieszEndpointScalar L 8 != 0.
```

Likewise, the exact finite-prime sampling of `h` inside `explicitCanonicalSourceMoment` does not determine `h^(7)(0)` without additional canonical structure.

**Consequence:** the FB-05 arithmetic problem cannot be closed merely by pointing to the square. The sign-bearing endpoint scalar or a separate sampling/cancellation relation must do genuine arithmetic work.

**Escape requirement:** prove a theorem-backed sign/nonvanishing property of the exact endpoint scalar, a canonical sample-to-jet rigidity statement, or another independent arithmetic restriction that composes with the retained state.

## OBS-041 — endpoint-scalar positivity is not by itself first-bad exclusion

**Status:** DERIVED FROM THE PROVED #163 RECURRENCE; RESEARCH PRIORITY CORRECTED BY PR #165.

On the retained even-selected shifted state, #163 gives

```text
2*(2*pi)^4*(R8-R9) = S8(L)*|h^(7)(0)|^2
```

with `R8 < 0` already theoremized. Therefore a hypothetical theorem

```text
S8(L) >= 0
```

would imply

```text
R9 <= R8 < 0,
```

not a contradiction.

PR #165 finds broad finite positive evidence for the exact executable `S8` normalization, but this does not change the logical point.

**Consequence:** endpoint-scalar sign/nonvanishing can be useful only after composition with another independent terminal restriction. Proving positivity merely because finite evidence looks favorable is not currently the highest-information theorem target.

## OBS-042 — direct whole-cell interval failure is not a sign result

**Status:** EXPERIMENTAL / CERTIFICATION-METHOD FIREWALL FROM PR #167.

For the near-critical canonical target

```text
Q=16, N=3, K*=4, parity=odd,
```

PR #167's direct fixed-cell Arb evaluation remained unresolved after depth-8 subdivision:

```text
256 / 256 leaves = UNRESOLVED.
```

No leaf was certified positive or bad.

Therefore:

```text
UNRESOLVED != negative
UNRESOLVED != positive
more subdivision != demonstrated mathematical progress
```

**Consequence:** change the representation rather than merely increasing interval depth. A scalar Sylvester/Schur pivot, channel decomposition, derivative/variation bounds, or another dependency-reduced formulation is the current escape.

## OBS-043 — isolated prime-entry stabilization does not control the full canonical aperture drift

**Status:** EXACT EXECUTABLE LOCAL STRUCTURE + FINITE ARB/FLOATING RESEARCH EVIDENCE FROM PR #168; NOT A LEAN THEOREM.

After enforcing the actual boundary-flat carrier before parity reduction, the executable source-atom expansion has first surviving orders

```text
odd  -> order 7 through M3^2
even -> order 9 through M4^2.
```

The canonical sign makes the entering odd prime-power contribution locally stabilizing at its first surviving order.

However the full canonical source also contains pole, archimedean, scalar-repair, and already-active prime-power terms whose aperture dependence is not delayed to the same high order.

PR #168 certifies the exact `L=log 17` threshold and 18 two-sided finite microscope points positive, while the full Q17 floating state still `CONTINUES_DOWN_BUT_POSITIVE`.

**Consequence:** a favorable local entering-prime jet does not imply favorable total aperture drift. The correct next object is a cancellation-preserving full scalar pivot/background decomposition, not the isolated atom by itself.

**Permanent warning:** do not formalize the isolated threshold jet and silently treat it as a full-source monotonicity/barrier theorem.

**RH remains OPEN.**
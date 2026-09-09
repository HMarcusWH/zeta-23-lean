# RHRC formal audit — theorem authority through PR #137; one-step determinant frontier synchronized

> **RH remains OPEN.**

## Current authority split

```text
live main after theorem PR #137 = fa2f209a6eb8b4059968e8d61239d80588ca256c
live main tree = e3de4dc0377f0124832822b6f97ab5bbd7718640

theorem-state anchor = PR #137 merge fa2f209a6eb8b4059968e8d61239d80588ca256c
validated theorem head = 64988e142590c82bd0ad43604279ede9a8e85eff
validated theorem tree = e3de4dc0377f0124832822b6f97ab5bbd7718640
theorem-bearing merged through = PR #137
RHRC #878 = SUCCESS
Permansson #651 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

Live GitHub head + exact compiler/CI evidence outrank this prose. Machine claim promotion remains a separate surface.

## Recent theorem-state progression

### PR #134 — zero-shift source transport

**PROVED:** denominator-free whole-kernel source transport, direct zero-shift cross-parity transfer, exact zero-shift `Gamma` overlap formula, and `Gamma0*mu(z)=0` on the full even predecessor kernel under the theorem hypotheses.

This closed the zero-shift transport bottleneck but did not give source sign, factor nonzeroness, branch exclusion, or RH.

### PR #136 — absolute canonical source energy

Exact theorem head: `0feb419dca7fe3f54c8654a323b1ea9489d1f369`.  
Merged theorem state: `3a6eb5e63e5c95f6e8b3fe3d4b78c203bb8b44a4`.  
Exact-head workflows: RHRC #877 = SUCCESS; Permansson #650 = SUCCESS.

**PROVED:**

- scalar-sensitive `matrixRealEnergy` algebra;
- identity-shift sensitivity;
- `sourceMatrix 1` energy acceptance test;
- exact canonical prime-energy atomization;
- exact archimedean energy split retaining the scalar correction;
- exact production canonical source-energy channel decomposition;
- parity-compressed and cubic-shell energy forms;
- regular zero-shift trial energy = `Re S0`;
- negative explicit Schur root -> negative absolute canonical trial energy.

**Not proved:** source-channel positivity, `q_c>=0`, one-step domination, branch exclusion, negative-root exclusion, RH.

### PR #137 — canonical one-step determinant reduction

Exact theorem head: `64988e142590c82bd0ad43604279ede9a8e85eff`.  
Merged theorem state: `fa2f209a6eb8b4059968e8d61239d80588ca256c`.  
Validated theorem tree: `e3de4dc0377f0124832822b6f97ab5bbd7718640`.

Exact-head workflows:

```text
RHRC #878 = SUCCESS
Permansson #651 = SUCCESS
```

**PROVED — source pairing and determinant objects.** `CanonicalSourcePairing.lean` exposes the exact complex production source pairing. `CanonicalOneStepDomination.lean` defines

```text
q_A(w) = Re<Aw,w>
b(w)   = <w,P_WTc>
q_c    = Re<Tc,c>
Δ(w)   = q_c*q_A(w) - |b(w)|^2
```

and rewrites these through the production source channels.

**PROVED — kernel annihilation from determinant sign.** If `Az=0` and `Δ(z)>=0`, then the full complex shell coupling vanishes.

**PROVED — domination removes zero-shift resonance.** `canonicalOneStepDomination` implies the shell coupling lies in `range A`, hence a zero-shift preimage exists. No zero-shift inverse, pseudoinverse or Laurent limit is used.

**PROVED — conditional endpoint sign and negative-root exclusion.** With predecessor nonnegativity, domination forces `Re S0>=0`; therefore no safe negative explicit Schur root can exist under domination.

**PROVED — exact failure form.**

```text
not canonicalOneStepDomination
  <-> q_c < 0 OR exists w, Δ(w) < 0.
```

**PROVED — global endpoint.** A hypothetical off-line zeta zero forces a global-first-bad predecessor-nonnegative canonical state where domination fails, and therefore forces the explicit sign-failure disjunction above.

**Not proved:** `canonicalOneStepDomination`; `q_c>=0`; `Δ(w)>=0` for all predecessor vectors; unconditional negative-root exclusion; terminal RH theorem.

## Current formal state

```text
off-line zero -> finite global first-bad state                         PROVED
negative exact secular/eigenvalue root                                 PROVED
both predecessor parities nonnegative                                  PROVED
zero-shift kernel/range + source transport                              PROVED
absolute canonical source energy/channel decomposition                  PROVED / #136
canonical complex source pairing                                        PROVED / #137
one-step determinant/channel decomposition                              PROVED / #137
domination -> zero-shift regularity + Re S0>=0                         PROVED / #137 CONDITIONAL
domination -> no safe negative explicit Schur root                     PROVED / #137 CONDITIONAL
off-line zero -> domination failure                                    PROVED / #137
off-line zero -> q_c<0 OR exists Δ<0                                  PROVED / #137

canonical shell-energy nonnegativity                                    OPEN
canonical determinant nonnegativity for all predecessor vectors         OPEN
canonical one-step domination                                           OPEN
negative-root exclusion                                                  OPEN
explicit terminal RH bridge                                              OPEN
RH                                                                       OPEN
```

## What changed mathematically

The active bottleneck is no longer “define an absolute energy” or “show domination would be sufficient.” Both are now theoremized. The remaining task is the source-specific sign theorem itself.

The most useful new theorem is the global finite **countercertificate**: any hypothetical off-line zero must create either negative canonical shell energy or a negative one-step determinant at the forced global-first-bad state. That sharply constrains where a counterexample to the intended positivity must live.

The reduction must not be oversold. Given `A>=0` and a one-dimensional shell, full one-step domination is essentially the missing positivity of the one-step block extension. #137 makes the arithmetic obligation exact; it does not remove its RH-level difficulty.

## Current research frontier

### A4b2b — canonical shell/determinant sign theorem

Under the exact first-bad-compatible canonical hypotheses, prove

```text
q_c >= 0
Δ(w) >= 0  for every w in W.
```

The proof must visibly use the canonical pole/arch/scalar/prime normalization. A generic Hermitian/parity/KKT argument is quarantined by existing exact countermodels.

### Source-structure subproblems

Promising representations to test before a full proof:

- a positive Gram/integral representation for `canonicalSourceChannelPairing`;
- a Cauchy-Schwarz remainder formula for `Δ`;
- exact cancellation of indefinite atom contributions after the full pole/arch/prime sum;
- high-order boundary-flat source-coordinate expansions targeted directly at `q_c` and `Δ`.

### A4R — optional regular-aperture log-lift

Still a fallback simplifier only. #137 already proves that domination itself removes zero-shift resonance, so A4R should be used only if it materially simplifies the source arithmetic.

## Falsification state

Before building a sign proof, search for canonical low-dimensional states satisfying the exact predecessor-nonnegative hypotheses with `q_c<0` or `Δ(w)<0`. Such a fixture would falsify this domination route, not RH.

Individual source atoms are known to be indefinite on legal vectors, so termwise positivity is not a credible proof plan. Any successful sign proof must use composition/cancellation in the full canonical source.

## Permanent firewalls

- compiler/CI validity is authoritative; repository presence alone is not;
- supporting theorem checks do not automatically imply machine claim promotion;
- `canonicalOneStepDomination` is not proved to hold;
- conditional negative-root exclusion is not unconditional exclusion;
- `q_c<0 OR exists Δ<0` is a forced witness, not a contradiction;
- source decomposition alone is not positivity;
- D is algebraic, not unitary/isometric;
- no `A^-1` at zero;
- no division by unproved source/transfer factors;
- generic countermodels do not refute the canonical arithmetic source;
- numerical precision is not theorem authority;
- RH remains OPEN.

Detailed current research implications: `research/RHRC/RESEARCH_LEADS_POST_137_DELTA.md`.

**RH remains OPEN.**

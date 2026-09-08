# R003 — CCM / finite Weil bridge

Status: **ACTIVE. GLOBAL FIRST-BAD + ZERO-SHIFT BRANCH RESPONSE + SOURCE-EXPLICIT CROSS-PARITY TRANSFER PROVED THROUGH PR #129; E4-A4 CANONICAL-SOURCE EXCLUSION CURRENT. RH OPEN.**

## Current authority split

```text
theorem-state anchor = PR #129 merge e1192857afed9f68fa4a13143ce690b62191b997
validated theorem head = 440be3e5b6bf05e94ae2c65b1704d52d20acc9af
theorem tree = 2f042a3b0b3313e7c67d627a58a32d579d4e7ff7
RHRC #838 = SUCCESS
Permansson #611 = SUCCESS

control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
Control v2 / FFBBP v1.6 hardened state = MERGED GREEN CONTROL INFRASTRUCTURE

RH = OPEN
```

Live GitHub head + exact Lean/CI build closure remain authoritative.

## Closed internal ladder

```text
F1 finite canonical obstruction                                  PROVED / #94
constrained / Euclidean finite wall                              PROVED / #96-#98
N-FLOW fixed-L negative tail                                     PROVED / #100
PARITY reversal / displacement collapse                          PROVED / #102
PARITY-FLOW D-equivalence / exact parity geometry                 PROVED / #103
PARITY-BAD least bad size + predecessor nonnegative               PROVED / #105
FIRST-BAD-SPECTRUM compression + negative mode                    PROVED / #107
FIRST-BAD-RIGIDITY-A/B shell projection + KKT                     PROVED / #109
FIRST-BAD-RIGIDITY-C cubic parity defect finrank <=1              PROVED / #110
FIRST-BAD-RIGIDITY-D1 global first bad + W/S + exact cubic F      PROVED / #112
FIRST-BAD-RIGIDITY-D2 V=W⊕S + shifted inverse + Schur             PROVED / #113
FIRST-BAD-RIGIDITY-E1 cubic generator not inherited               PROVED / #115
FIRST-BAD-RIGIDITY-E2 canonical cubic quotient + normalized Schur PROVED / #118
FIRST-BAD-RIGIDITY-E3-A exact negative secular root iff eigenmode PROVED / #119
FIRST-BAD-RIGIDITY-E3-B2 exact explicit Schur scalar bridge       PROVED / #121
FIRST-BAD-RIGIDITY-E3-B1 projected metric/resolvent control       PROVED / #122
FIRST-BAD-RIGIDITY-E4-A1 ker(A) cubic-coupling classification     PROVED / #122
FIRST-BAD-RIGIDITY-E4-A2 kernel/range zero-shift dichotomy        PROVED / #124
FIRST-BAD-RIGIDITY-E4-A2 canonical endpoint + complete square     PROVED / #125
FIRST-BAD-RIGIDITY-E4-A3a canonical zero-shift shell response     PROVED / #127
FIRST-BAD-RIGIDITY-E4-A3b signed response + canonical kernel pole PROVED / #128
FIRST-BAD-RIGIDITY-E4-A3c source-explicit parity transfer         PROVED / #129
off-line zero -> source-explicit first-bad certificate            PROVED / #129
```

## Exact post-#129 first-bad state

A hypothetical off-critical-line zeta zero forces one finite problem with:

- positive aperture `L`;
- global least-bad successor size;
- both predecessor parity sectors nonnegative;
- a genuine negative parity-compressed eigenvalue `lam<0`;
- intrinsic successor decomposition `V=W⊕S`, `dim_C S=1`;
- canonical cubic shell vector `c!=0`;
- canonical quotient coordinate on `V/W`;
- safe shifted predecessor inverse `R_lam=(A-lam I)^(-1)`;
- exact quotient and explicit real Schur scalar root;
- exact kernel/range split `W=ker A⊕range A`;
- exact regular/resonant zero-shift classification;
- exact #127 shell response;
- exact #128 canonical kernel pole;
- exact #129 source-explicit parity transfer.

The branch package is:

```text
REGULAR:
  Ax0=b
  S0=<Tc,c>-<x0,b>
  u0=-x0+c
  sigma0*c = T u0
  S0=star(sigma0)<c,c>
  Re S0<0
  Re sigma0<0
  k=K(b)=0

RESONANT:
  k=K(b)!=0
  (-lam)K(R_lam b)=k
  K(R_lam b)=(-lam)^(-1)k
  plus the #124 pointwise witness / identity / bound.
```

Across parity, define the #129 canonical source moment

```text
sourceMoment(v)
  = <n2, canonicalSourceMatrix(L,N+1)v>/<n2,n2>.
```

Then the exact secular transfer is

```text
F_- = alpha * F_+ + Gamma * sourceMoment(u_+).
```

`Gamma` is theorem-identified with an odd trial/cubic overlap ratio. At an even root, `F_+=0` and `F_-` is exactly overlap times source moment. At an odd root, `F_-=0` and the full transfer balance is retained without division.

This is a finite-dimensional rigidity/source-exposure package, not an RH proof.

## E4-A3 settlement

**PROVED / #127-#129.**

The old A3 implementation obligations are closed:

- shell response is theoremized;
- the regular response sign is theoremized;
- the resonant kernel pole is theoremized;
- exact quotient/D transport is theoremized;
- the predecessor correction in `D c+` is theoremized and retained;
- the exact cross-parity secular equation is theoremized;
- the cubic defect coefficient is identified with the actual canonical source moment;
- the global off-line-zero wrapper carries the source-explicit certificate.

None of these results excludes the bad state by itself.

## Current route state — E4-A4 canonical-source branch exclusion

### A4a — source moment decomposition

**OPEN / PRIMARY.**

Open the production definition of `canonicalSourceMatrix` inside

```text
evenQuadraticSourceMoment L (N+1) uPlus.
```

The first target should be an exact formula: isolate constant-normal cancellation and identify the actual source-channel contributions seen by `n2`. Avoid starting with a guessed inequality.

### A4b — regular branch source test

**OPEN.**

Use the theorem-backed package

```text
k=0
Re sigma0<0
F_- = alpha F_+ + Gamma sourceMoment(u_+)
```

and the actual source formula. The objective is either a contradiction or a strictly smaller canonical regular class.

Do not assume or divide by `alpha`, `Gamma`, the overlap or `sourceMoment` without separate proof.

### A4c — resonant branch source test

**OPEN.**

Use

```text
k!=0
(-lam)K(R_lam b)=k
F_- = alpha F_+ + Gamma sourceMoment(u_+)
```

plus predecessor nonnegativity and actual source values.

The exact pole is classification, not contradiction. The theorem must identify a source-specific incompatibility.

### A4d — global first-bad exclusion

**OPEN.**

Only after both canonical branches are excluded should the route theoremize no negative global first-bad root. The existing ExceptionalZero reduction already starts from an arbitrary off-line zero, so that exclusion would immediately rule out such a zero in the project's zeta carrier. A final explicit bridge to the terminal Mathlib `RiemannHypothesis` statement would still be required.

## Post-#129 generic-route falsification

The active route changed because generic structural countermodels survived:

- negative regular Schur endpoint with nonnegative predecessor;
- exact zero resonance with negative spectrum;
- actual centered-grid boundary-flat parity spaces with generic reversal-symmetric diagonal operators producing both-parity regular negativity, one-parity badness, or genuine resonance;
- displacement-preserving diagonal perturbations changing the sign-sensitive finite state.

These are **EXPERIMENTAL SIGNAL / synthetic falsification fixtures**, not canonical CCM counterexamples.

**Route rule:** a proposed contradiction that does not use source values beyond Hermitianity/parity/displacement should first be tested against `../../countermodels/POST_129_STRUCTURAL_COUNTERMODELS_2026_09_08.md`.

## E4-B — parity shifted-nullity

**OPEN / PARALLEL.**

Use the existing algebraic D-equivalence and same-space parity defect with finrank <=1 to theoremize a shifted-nullity comparison. Do not import unitary interlacing through D. Activate only if it constrains A4.

## E3-C — monotonicity / root-count control

**OPEN / PARALLEL.**

The exact root detector is a real explicit scalar on `lam<0`. A shifted-resolvent identity may yield strict monotonicity and at most one negative root.

Permanent firewall:

```text
at most one negative root != no negative root.
```

## E3-B3 — general predecessor-floor theorem

**LEAD / OPEN FORMALIZATION.**

Generalize the #122 `mu=0` metric estimate. Under

```text
mu ||w||^2 <= Re <Aw,w>,
lam<mu,
```

prove the denominator `mu-lam` resolvent estimate and derive

```text
d_N(g_N+d_N) <= beta_N^2.
```

The shortcut `d_N<=beta_N^2/g_N` requires separately proved `g_N>0`.

## Deformation-budget composition and falsification lane

The theorem-backed ancestry is now

```text
#119 exact root detector
  -> #121 explicit Schur bridge
  -> #122 real metric/resolvent control
  -> #124/#125 zero-shift branch endpoint
  -> #127 shell response
  -> #128 signed response / canonical pole
  -> #129 source-explicit cross-parity transfer
  -> E4-A4 canonical-source exclusion.
```

The cheap diagnostic order remains

```text
g_N=q_N-mu_N
beta_N
beta_N^2/g_N.
```

Kill the lane if the gap fails, coupling does not decay usefully, or the ratio cannot support a complete summable certified tail. A finite prefix, fitted tail or local residual is not a complete budget.

## Source-faithful parallel lane

The independent source-faithful lane remains

```text
G1-B1B -> G1-final -> S-NEG -> G23.
```

Do not conflate source interface geometry with source negativity.

## Permanent normalization / model firewalls

- canonical sign-sensitive object is `canonicalSourceMatrix = cutoffFreeMatrix = sourceEq44Matrix = dictionaryMatrix` under the repaired source convention;
- legacy printed `finiteMatrix` differs by a scalar identity, so absolute eigenvalue/PSD/inertia claims do not transfer automatically;
- generic R002 smooth taper-grid is not the canonical CCM family except at exact specialization;
- Bombieri zero-height truncations are distinct from deterministic CCM Fourier-mode truncations;
- boundary-flat legality is required for the hard-window C² bridge;
- `ker A` is not the predecessor-size compressed-operator kernel;
- no `A^-1` at zero;
- `Re S0<0` and `Re sigma0<0` are not branch exclusion;
- the exact resonant pole is not automatically contradictory;
- D is algebraic, not unitary/isometric;
- the predecessor correction in `D c+` may not be dropped;
- #129 proves no sign/nonzeroness for `alpha`, `Gamma`, overlap or source moment;
- generic structural countermodels do not refute `canonicalSourceMatrix`;
- root uniqueness is not root exclusion;
- RH remains OPEN.

Detailed current implications and falsification plan: `../../RESEARCH_LEADS_POST_129_DELTA.md`.

**RH remains OPEN.**
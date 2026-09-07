# R003 — CCM / finite Weil bridge

Status: **ACTIVE. GLOBAL FIRST-BAD + EXACT REAL SECULAR METRIC/RESONANCE PACKAGE PROVED THROUGH PR #122; E4-A2 ZERO-SHIFT ENDPOINT CURRENT. RH OPEN.**

## Current authority split

```text
theorem-state anchor = PR #122 merge b2d1210902d430f3cdd3c24c2961ab843469b5d6
validated theorem head = 9c8154e3ea7a5762f8e65d508dc68bb9246db869
theorem tree = db51419fb7cc8b2e3dbe5cf2e770390086db9862
theorem-bearing merged through = PR #122
E3-B1 metric control + E4-A1 zero-resonance coupling classification = PROVED / MERGED

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
off-line zero -> common global-first-bad metric/resonance package PROVED / #122
```

## Exact post-#122 first-bad state

A hypothetical off-critical-line zeta zero forces one finite problem with:

- positive aperture `L`;
- global least-bad successor size;
- both predecessor parity sectors nonnegative;
- a genuine negative parity-compressed eigenvalue `lam<0`;
- intrinsic successor decomposition `V=W⊕S`, `dim_C S=1`;
- canonical cubic shell vector `c=intrinsicCubicShellPart` with `c!=0`;
- canonical quotient coordinate on `V/W`;
- safe shifted predecessor inverse `R_lam=(A-lam I)^(-1)`;
- canonical trial vector `u_lam=-R_lam Bc+c`;
- exact quotient scalar `F(lam)` with root iff genuine eigenmode;
- explicit Schur scalar

  ```text
  S(lam)=<Tc,c>-lam<c,c>-<R_lam Bc,Bc>;
  ```

- exact real pointwise identity

  ```text
  F(lam)=S(lam)/<c,c>;
  ```

- real/nonnegative resolvent quadratic value and denominator-free metric bounds;
- at a root,

  ```text
  0 <= Re(<Tc,c>-lam<c,c>)
  (-lam) Re(<Tc,c>-lam<c,c>) <= ||Bc||^2;
  ```

- exact E4-A1 kernel-coupling classification

  ```text
  Az=0 -> (<z,Bc>=0 <-> Tz=0).
  ```

This is a finite-dimensional rigidity package, not an RH proof.

## E3-B settlement — explicit real secular metric

**PROVED / #121-#122.**

PR #121 theoremizes the conjugated explicit scalar bridge. PR #122 supplies the projected predecessor symmetry, shifted coercivity, resolvent symmetry/positivity/bounds and realness needed to remove the conjugation in the safe negative-shift regime.

The exact #119 root detector and the explicit Schur scalar can now be analyzed as one real scalar object under the proved hypotheses.

## E4-A1 settlement — zero-resonance coupling

**PROVED / #122.**

For

```text
A=P_W T|_W,
c=intrinsicCubicShellPart,
b=Bc,
```

if `Az=0`, then `Tz` lies in the one-dimensional intrinsic shell and

```text
<z,b> = star(kappa(Tz)) <c,c>.
```

Therefore

```text
Az=0 -> (<z,b>=0 <-> Tz=0).
```

The quantified version says `b` annihilates the full projected kernel iff every projected-kernel vector is a genuine successor zero mode.

### Semantic firewall

This does not prove that `b` annihilates `ker A`. `ker A` is the kernel of the projected successor predecessor block, not the predecessor-size compressed operator.

## Current route state — E4-A2 zero-shift endpoint

### Branch A — decoupled kernel

**DERIVED / OPEN FORMALIZATION.**

Assume the E4-A1 vanishing side:

```text
∀ z, Az=0 -> <z,b>=0.
```

Use finite-dimensional symmetry to prove

```text
b ∈ range A,
```

then choose `x0` with `A x0=b`. Build the zero-shift endpoint from this solution, proving independence of the chosen solution from the kernel ambiguity. Never introduce `A^-1` at zero.

### Branch B — resonant kernel

**LEAD / OPEN.**

Assume there exists `z` with

```text
Az=0
<z,b>!=0.
```

PR #122 implies `Tz!=0` and that the image is a nonzero shell direction. The next theorem should isolate the corresponding `1/(-lam)` zero-eigenspace contribution to `R_lam b` and derive a useful sign/asymptotic restriction on `S(lam)` near zero.

This branch may force a negative secular root rather than exclude one; that possibility is itself valuable because it would classify which first-bad configurations remain admissible.

## E3-C — monotonicity / root-count control

**OPEN; now unblocked by the scalar representation.**

Prove a finite-dimensional shifted-resolvent identity and derive strict monotonicity of the exact real explicit secular scalar if justified.

Expected consequence:

```text
at most one negative root.
```

Permanent firewall:

```text
at most one negative root != no negative root.
```

## E4-B — parity shifted-nullity

**OPEN / PARALLEL.**

Use the existing algebraic D-equivalence and same-space parity defect with finrank <=1 to theoremize a shifted-nullity comparison. Do not import unitary interlacing through D; D is not theoremized as isometric.

## E3-B3 — general predecessor-floor theorem

**LEAD / OPEN FORMALIZATION.**

Generalize the #122 `mu=0` metric estimate. Under

```text
mu ||w||^2 <= Re <Aw,w>,
lam<mu,
```

prove the denominator `mu-lam` resolvent estimate and derive the canonical one-step inequality

```text
d_N(g_N+d_N) <= beta_N^2.
```

The shortcut `d_N<=beta_N^2/g_N` requires separately proved `g_N>0`.

## Deformation-budget composition and falsification lane

The theorem-backed metric ancestry is now

```text
#119 exact root detector
  -> #121 explicit Schur bridge
  -> #122 real metric/resolvent control
  -> E3-B3 general lower-floor theorem if needed.
```

The cheap diagnostic order remains

```text
g_N=q_N-mu_N
beta_N
beta_N^2/g_N.
```

Kill the route if the gap fails, coupling does not decay usefully, or the ratio cannot support a complete summable certified tail. A finite prefix, fitted tail or local residual is not a complete budget.

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
- E4-A1 classification does not imply kernel decoupling;
- no `A^-1` at zero;
- #122 metric control and any future uniqueness theorem are not negative-root exclusion;
- RH remains OPEN.

Detailed current implications and falsification plan: `../../RESEARCH_LEADS_POST_122_DELTA.md`.

**RH remains OPEN.**
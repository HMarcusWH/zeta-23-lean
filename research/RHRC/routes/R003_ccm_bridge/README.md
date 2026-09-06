# R003 — CCM / finite Weil bridge

Status: **ACTIVE. GLOBAL FIRST-BAD + CANONICAL SECULAR REDUCTION PROVED THROUGH PR #119; E3-B METRIC BRIDGE CURRENT. RH OPEN.**

## Current authority split

```text
theorem-state anchor = PR #119 merge d4175d2bb305e62863f593824b3f40e921a46ee6
theorem tree = 1985472ac470822af279044261fa365fb9bb5535
theorem-bearing merged through = PR #119
E3-A exact canonical secular root/eigenmode equivalence = PROVED / MERGED

control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
Control v2 / FFBBP v1.6 hardened state = MERGED GREEN CONTROL INFRASTRUCTURE

RH = OPEN
```

Live GitHub head + exact Lean/CI build closure remain authoritative.

## Closed internal ladder

```text
F1 finite canonical obstruction                                PROVED / #94
constrained / Euclidean finite wall                            PROVED / #96-#98
N-FLOW fixed-L negative tail                                   PROVED / #100
PARITY reversal / displacement collapse                        PROVED / #102
PARITY-FLOW D-equivalence / exact parity geometry               PROVED / #103
PARITY-BAD least bad size + predecessor nonnegative             PROVED / #105
FIRST-BAD-SPECTRUM compression + negative mode                  PROVED / #107
FIRST-BAD-RIGIDITY-A/B shell projection + KKT                   PROVED / #109
FIRST-BAD-RIGIDITY-C cubic parity defect finrank <=1            PROVED / #110
FIRST-BAD-RIGIDITY-D1 global first bad + W/S + exact cubic F    PROVED / #112
FIRST-BAD-RIGIDITY-D2 V=W⊕S + shifted inverse + Schur           PROVED / #113
FIRST-BAD-RIGIDITY-E1 cubic generator not inherited             PROVED / #115
FIRST-BAD-RIGIDITY-E2 canonical cubic quotient + normalized Schur PROVED / #118
FIRST-BAD-RIGIDITY-E3-A exact negative secular root iff eigenmode PROVED / #119
off-line zero -> common global-first-bad negative secular root   PROVED / #119
```

## Exact post-#119 first-bad state

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
- residual `r_lam=T u_lam-lam u_lam` with zero predecessor coordinate;
- exact criterion `cubicSecularScalar(lam)=0 <-> r_lam=0 <-> lam is an eigenvalue`;
- exact parity KKT residual and cubic one-channel factorization inherited from the earlier first-bad package.

This is a finite-dimensional rigidity package, not an RH proof.

## E2 settlement — canonical quotient coordinate

**PROVED / #118.**

The canonical cubic shell vector is a faithful coordinate on the one-dimensional intrinsic shell. Every shell vector reconstructs from one complex scalar, quotient coordinate zero is exactly predecessor membership, and genuine negative eigenmodes normalize canonically to shell part `c`.

On the odd carrier the exact cubic parity-defect functional is also the canonical quotient coordinate of the exact intertwining defect.

Firewalls remain: no shell invariance, no D-unitarity, no theorem that the cubic defect functional is nonzero on a chosen input.

## E3-A settlement — exact canonical secular equation

**PROVED / #119.**

For each safe real `lam<0` under predecessor nonnegativity, define

```text
u_lam = -(A-lam I)^(-1)Bc + c
r_lam = T u_lam - lam u_lam
F(lam) = intrinsicCubicQuotientCoordinate(r_lam).
```

The predecessor part of `r_lam` is exactly zero, and the quotient coordinate is faithful on the remaining one-dimensional shell direction. Therefore

```text
F(lam)=0 <-> r_lam=0
```

and hence

```text
F(lam)=0
  <-> exists nonzero v, T v = lam v.
```

Any genuine negative eigenmode canonically normalizes to the same trial vector.

### Representation firewall

`F(lam)` is the quotient coordinate of the full residual. The old explicit Schur expression

```text
<Tc,c> - lam<c,c> - <R_lam Bc,Bc>
```

is known to vanish for genuine eigenmodes, but pointwise equality between this expression (after the correct canonical normalization) and `F(lam)` is not yet a theorem.

Do not transfer sign, reality or monotonicity between the two representations without the E3-B bridge.

## Current route state — E3-B metric bridge

### E3-B1 — projected predecessor symmetry / coercivity

**DERIVED / OPEN FORMALIZATION.**

Targets:

```text
A = P_W T|_W is symmetric
A-lam I is symmetric for real lam
(-lam)||w||^2 <= Re <(A-lam I)w,w>        for lam<0
||R_lam b|| <= ||b||/(-lam)
0 <= Re <R_lam b,b> <= ||b||^2/(-lam)
```

Prefer proofs directly from existing `parityCompressedCanonical_isSymmetric`, W/S orthogonality, predecessor nonnegativity and the existing shifted equivalence. Avoid unnecessary self-adjoint-operator abstraction.

### E3-B2 — explicit secular bridge

**DERIVED / OPEN FORMALIZATION.**

Use the canonical cubic shell vector and the repository's exact complex-inner-product convention to prove pointwise that the #119 quotient scalar equals the correctly normalized explicit Schur scalar.

Only then can realness/sign/monotonicity statements about the explicit expression become theorem statements about the exact #119 root detector.

### E3-B3 — quantitative predecessor-floor theorem

**LEAD / OPEN FORMALIZATION.**

Under an independently certified predecessor floor

```text
mu ||w||^2 <= Re <Aw,w>,
```

for `lam<mu` prove the stronger resolvent estimate with denominator `mu-lam`. Then use

```text
q_N = Re <Tc,c>/||c||^2
beta_N^2 = ||Bc||^2/||c||^2
```

to derive at a secular root

```text
d_N(g_N+d_N) <= beta_N^2,
```

where

```text
d_N=mu_N-lam
g_N=q_N-mu_N.
```

The shortcut `d_N<=beta_N^2/g_N` requires separately proved `g_N>0`.

## E4-A — zero resonance / parity nullity

**OPEN / HIGH PRIORITY PARALLEL.**

Global-first-bad provides `A>=0`, not `A>0`. Thus `ker A` may be nontrivial and the negative-shift resolvent can diverge near zero.

The central kernel-coupling question is

```text
z in ker A -> <z,Bc>=0 ?
```

If true, the zero eigenspace decouples from the canonical secular channel. If false, the resonant singular contribution may itself provide a rigidity signal.

In parallel, use the existing algebraic D-equivalence and same-space parity defect with finrank <=1 to theoremize a shifted-nullity comparison such as

```text
|nullity(T_even-zI)-nullity(T_odd-zI)| <= 1.
```

Do not import unitary interlacing through D; D is not theoremized as isometric.

## E3-C — monotonicity / root-count control

**OPEN; downstream of E3-B/E4.**

Prefer an algebraic resolvent identity before calculus. If symmetry/positivity permits, derive monotonicity of the explicit real secular scalar on the negative axis and at most one negative root.

Permanent firewall:

```text
at most one negative root != no negative root.
```

A final contradiction requires additional CCM-specific shell/parity/KKT/N-flow structure.

## Deformation-budget composition and falsification lane

The theorem and diagnostic lanes now meet at E3-B rather than at an unproved E2 interface.

The cheap diagnostic order remains

```text
g_N=q_N-mu_N
beta_N
beta_N^2/g_N.
```

Kill the route if the gap fails, coupling does not decay usefully, or the ratio cannot support a complete summable certified tail. A finite prefix, fitted tail or local residual is not a complete budget.

Exact N-flow badness persistence means a genuine certified positive horizon would eliminate the whole fixed-`(L,p)` N-axis. All-L coverage / controlled L-dependence is still required eventually.

## Source-faithful parallel lane

The internal F1/first-bad route has bypassed the old need for source negativity before finite progress, but the independent source-faithful lane remains useful as a cross-check:

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
- #119 exact secular equivalence is not negative-root exclusion;
- predecessor nonnegative is not predecessor strictly positive;
- no `A^-1` at zero;
- RH remains OPEN.

Detailed current implications and falsification plan: `../../RESEARCH_LEADS_POST_119_DELTA.md`.

**RH remains OPEN.**
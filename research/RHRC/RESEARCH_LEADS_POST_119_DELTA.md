# RHRC research leads delta — post PR #119

> **Claim firewall: RH remains OPEN.**
>
> This file records the post-green mathematical consequences of merged PRs #118/#119 and supersedes `RESEARCH_LEADS_POST_116_DELTA.md` for current execution priority. It is a research delta, not a theorem registry. Exact Lean/compiler/CI evidence remains authoritative.

## Exact authority split

```text
live main after #119 = d4175d2bb305e62863f593824b3f40e921a46ee6
live main tree = 1985472ac470822af279044261fa365fb9bb5535

theorem-state anchor = PR #119 merge d4175d2bb305e62863f593824b3f40e921a46ee6
theorem tree = 1985472ac470822af279044261fa365fb9bb5535
validated theorem head = 2c18909710d9dab0a111849a7c6160be8736e541
E3-A exact canonical negative secular root/eigenmode equivalence = PROVED / MERGED

control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
Control v2 / FFBBP v1.6 hardened state = MERGED GREEN CONTROL INFRASTRUCTURE

RH = OPEN
```

---

# What became formally true

## PROVED — PR #118: canonical cubic shell/quotient coordinate

The intrinsic successor shell `S` is one-dimensional and the canonical cubic shell vector `c_N` is nonzero. PR #118 uses `c_N` as the distinguished coordinate direction and proves:

```text
kappa_S : S -> C
kappa_S(s) * c_N = s
kappa_S(s)=0 <-> s=0.
```

Composing with `intrinsicShellPart` gives a canonical quotient coordinate

```text
kappa_N : V_(N+1) -> C
```

with

```text
kappa_N(v)=0 <-> v in W_N.
```

The canonical successor cubic vector has quotient coordinate one.

On the odd carrier PR #118 also proves that the exact cubic parity-defect functional is literally the quotient coordinate of the exact intertwining defect in the unique new N-flow direction.

For a genuine negative first-bad eigenmode `v`, `kappa_N(v) != 0`; scaling the whole eigenmode by its inverse produces a canonical normalized eigenvector whose shell component is exactly `c_N`.

## PROVED — PR #119: exact canonical secular criterion

For every safe real negative shift `lam<0` under predecessor nonnegativity, define

```text
A = intrinsicPredecessorBlock
B = intrinsicShellToPredecessor
c = intrinsicCubicShellPart
R_lam = (A-lam I)^(-1)

u_lam = -R_lam(Bc) + c
r_lam = T u_lam - lam u_lam.
```

PR #119 proves:

```text
intrinsicPredecessorPart(r_lam)=0.
```

The canonical secular scalar is

```text
F(lam)=intrinsicCubicQuotientCoordinate(r_lam).
```

Because the residual has no predecessor component and the cubic coordinate is faithful on the one-dimensional shell,

```text
F(lam)=0 <-> r_lam=0.
```

Hence

```text
F(lam)=0
  <-> u_lam is a genuine eigenmode
  <-> exists nonzero v, T v = lam v.
```

Any genuine negative eigenmode canonically normalizes to `u_lam`.

The ExceptionalZero endpoint composes this with the existing off-line-zero -> global-first-bad chain, so a hypothetical off-critical-line zeta zero forces one global-first-bad finite state with an exact negative root of `F`.

**RH remains OPEN.**

---

# What changed

Before #118/#119 the project had:

```text
negative eigenmode
  -> nonzero shell component
  -> shifted predecessor reconstruction
  -> scalar Schur identity.
```

This was a one-way necessary reduction.

After #118/#119 the project has:

```text
canonical one-dimensional quotient coordinate
+ canonical shell normalization
+ canonical shifted-resolvent trial vector
+ full residual with zero predecessor part

=> exact scalar root <-> full residual zero <-> eigenmode.
```

The negative spectral problem at a first-bad successor is therefore genuinely reduced to a one-variable canonical scalar root problem on the safe negative axis.

This is stronger than the old shifted Schur identity, but it is still not a contradiction.

---

# Upstream implications

## L-119-U1 — projected predecessor block is now the natural metric primitive

**Research status:** READY / CURRENT  
**Formal status:** DERIVED / OPEN FORMALIZATION

The next useful abstraction is not another shell basis or generic Feshbach package. The already-defined

```text
A = intrinsicPredecessorBlock = P_W T|_W
```

should receive the smallest native metric theorem surface:

```text
A symmetric
A-lam I symmetric for real lam
(-lam)||w||^2 <= Re <(A-lam I)w,w>  for lam<0
||R_lam b|| <= ||b||/(-lam).
```

These statements should follow from:

- full parity-compression symmetry already proved in #107;
- W/S orthogonality from #113;
- predecessor nonnegativity from the global-first-bad package;
- the existing finite-dimensional shifted equivalence.

**Design rule:** do not build a larger self-adjoint-operator hierarchy unless Lean forces it.

## L-119-U2 — general lower-floor version is more reusable than only `A>=0`

**Research status:** READY AFTER E3-B1  
**Formal status:** LEAD / HYPOTHESIS

A reusable theorem should accept a quantitative lower floor

```text
mu ||w||^2 <= Re <Aw,w>
```

and prove, for `lam<mu`,

```text
(mu-lam)||R_lam b|| <= ||b||
Re <R_lam b,b> <= ||b||^2/(mu-lam).
```

The first-bad predecessor supplies only the special case `mu=0`; later certified finite spectral floors may provide stronger input.

This avoids baking a semidefinite-only bound into the final interface.

---

# Downstream implications

## L-119-D1 — pointwise explicit secular bridge

**Research status:** HIGHEST-PRIORITY THEOREM TARGET  
**Formal status:** DERIVED / OPEN FORMALIZATION

PR #119 defines the exact root detector by quotient coordinate of the full residual. PR #113/#118 provide the explicit canonical cubic-shell Schur expression

```text
S(lam) =
  <Tc,c>
  - lam<c,c>
  - <R_lam Bc,Bc>.
```

On genuine eigenmodes `S(lam)=0` is already proved. What is not yet proved is the pointwise identity for every safe negative shift between `F(lam)` and the correctly normalized `S(lam)`.

The expected canonical normalized scalar is

```text
Sigma(lam) = S(lam) / <c,c>
```

up to the exact orientation/conjugation forced by Mathlib's convention that the complex inner product is linear in the second argument.

Target:

```text
F(lam)=Sigma(lam).
```

**Why this matters:** `F` has the exact root/eigenmode iff; `Sigma` exposes resolvent positivity and scalar analysis. The pointwise bridge is what lets those two strengths compose.

## L-119-D2 — theorem-backed one-step deformation inequality

**Research status:** ACTIVE COMPOSITION  
**Formal status:** LEAD / HYPOTHESIS

With a certified predecessor floor `mu`, define scale-free canonical shell quantities

```text
q_N = Re <Tc,c> / ||c||^2
beta_N^2 = ||Bc||^2 / ||c||^2

d_N = mu_N-lam
g_N = q_N-mu_N.
```

At a negative secular root, the explicit Schur equation plus the floor-resolvent estimate should imply

```text
g_N+d_N <= beta_N^2/d_N
```

and therefore

```text
d_N(g_N+d_N) <= beta_N^2.
```

If `g_N>0` is independently certified,

```text
d_N <= beta_N^2/g_N.
```

This is now the mathematically proper ancestry for the Control-v2 deformation-budget diagnostic.

## L-119-D3 — root count becomes a theorem target only after the metric bridge

**Research status:** BLOCKED ON E3-B/E4  
**Formal status:** OPEN

Once the explicit real scalar is theorem-identified with `F`, prove the shifted resolvent identity algebraically and test whether

```text
lam -> Re <R_lam b,b>
```

has the order behavior needed for monotonicity of the secular scalar on the negative axis.

A successful theorem may imply at most one negative root or negative-index control.

**Firewall:** root uniqueness is not root absence.

---

# Resurrected routes

## L-119-R1 — parity rank-one route now talks to the exact secular coordinate

**Research status:** RESURRECTED / ACTIVE PARALLEL  
**Formal status:** LEAD / HYPOTHESIS

PR #110 proved that the even/odd compressed parity defect is algebraically one-channel / finrank at most one after D-transport. At the time this did not supply a canonical metric shell coordinate.

PR #118 now identifies the unique new quotient direction canonically, and PR #119 identifies the successor negative spectral obstruction canonically by one scalar root.

Therefore the old parity rank-one information may now be composable with the first-bad secular equation rather than used only as an abstract rank bound.

Immediate algebraic target:

```text
rank(T_odd^D - T_even) <= 1
  -> |nullity(T_odd^D-zI)-nullity(T_even-zI)| <= 1.
```

This requires no unitary D and should be attacked as finite-dimensional rank/kernel algebra.

## L-119-R2 — simultaneous parity resonance becomes a zero-resonance diagnostic

**Research status:** RESURRECTED / REFRAMED  
**Formal status:** OPEN

The old E4 simultaneous-resonance question is no longer merely about comparing even/odd spectra. It may control the singular part of the predecessor resolvent near zero.

This gives the parity-nullity route a direct role in the E3 secular analysis.

DR-010 remains dead: none of this uses fitted small commutators or eigenvector convergence.

---

# New RH-relevant clues

## L-119-C1 — kernel-coupling decoupling

**Research status:** HIGH-VALUE LEAD  
**Formal status:** LEAD / HYPOTHESIS

Global-first-bad gives only `A>=0`. Thus the safe negative-shift resolvent can have a `1/(-lam)` singularity on `ker A` as `lam -> 0-`.

The most direct structural question is

```text
z in ker A -> <z,Bc>=0 ?
```

Equivalently, does the canonical shell coupling avoid the zero eigenspace of the predecessor block?

If YES:

- the singular zero eigenspace decouples from the scalar secular channel;
- one may restrict resolvent control to the positive spectral complement;
- the effective denominator can be a positive nonzero spectral floor there.

If NO:

- the secular term has a forced singular contribution near zero;
- that singular asymptotic may constrain root location or parity resonance.

Either outcome is informative.

## L-119-C2 — quotient scalar and cubic defect coordinate may compare across parity

**Research status:** LEAD  
**Formal status:** OPEN

PR #118 identifies the odd intertwining defect's quotient coordinate with `cubicDefectFunctional`. PR #119 defines the successor spectral residual's quotient coordinate as the exact secular scalar.

Both are now coordinates in the same type of canonical one-step quotient.

A potentially useful composition is to ask whether the parity intertwining relation induces a direct algebraic relation between the even and odd secular scalars at a common shift.

This was not available before the canonical quotient coordinate existed.

No equal-spectrum or unitary statement is implied.

## L-119-C3 — attack the constrained block counterexample space

**Research status:** ACTIVE CREATIVE LEAD  
**Formal status:** OPEN

Rather than asking immediately for RH, formulate the finite countermodel problem:

> Does there exist a finite Hermitian block system satisfying all theorem-backed CCM constraints simultaneously — exact centered N-flow ancestry, global-first-bad predecessor nonnegativity, one-dimensional canonical shell, KKT, parity rank-one/cubic factorization, canonical quotient coordinate, and exact secular root — with a negative root?

If a generic finite block counterexample survives all currently formalized constraints, the next theorem must add genuinely CCM-specific information.

If no such constrained countermodel exists, its proof shape may reveal the missing Lean theorem.

---

# Falsification checks

## F-119-01 — do not conflate the two scalarizations

`cubicSecularScalar` is not definitionally the old Schur inner-product expression. The pointwise bridge must be theoremized.

## F-119-02 — predecessor nonnegative is not predecessor positive

A zero kernel is allowed by current hypotheses. Any denominator stronger than `-lam` must come from an independently proved lower floor or a kernel-decoupling theorem.

## F-119-03 — no `A^-1` at zero

Only `A-lam I` for safe negative shifts is currently invertible.

## F-119-04 — inner-product convention

Mathlib's complex inner product is linear in the second argument. Conjugation/orientation mistakes can silently change the explicit scalar formula.

## F-119-05 — D is algebraic, not unitary

Parity nullity comparison may use rank/kernel algebra. Hermitian interlacing, metric transport and equal-spectrum statements through D remain forbidden without a new theorem.

## F-119-06 — uniqueness is not exclusion

Even a strictly monotone secular scalar can have one negative root. A final contradiction requires endpoint/sign information or additional CCM-specific rigidity.

## F-119-07 — diagnostic deformation formulas remain subordinate to theorem hypotheses

`beta_N^2/g_N` is valid as a proof ingredient only after `g_N>0` is independently certified and the operator inequality is theoremized.

## F-119-08 — finite/fitted tails remain non-certificates

No finite prefix, fitted asymptotic, local residual or apparent convergence certifies the complete infinite tail.

## F-119-09 — normalization/source firewall unchanged

No #118/#119 theorem changes the canonical/legacy source normalization distinction.

## F-119-10 — RH claim firewall

Green secular reduction != root exclusion != positivity != finite-to-infinite closure != RH.

---

# Highest-leverage next moves

```text
1. E3-B1 projected predecessor symmetry + shifted coercivity/resolvent bounds
2. E3-B2 exact pointwise bridge: quotient secular scalar = normalized explicit Schur scalar
3. E4-A generic rank-one shifted-nullity theorem + predecessor zero-resonance/kernel-coupling analysis
4. E3-B3 quantitative predecessor-floor one-step deformation inequality
5. E3-C resolvent identity / monotonicity / root-count control if the bridge supports it
6. constrained CCM negative-root countermodel/exclusion test
7. only then invest in a complete all-L deformation horizon if the paper diagnostics survive
```

Mathematical information gain should outrank implementation convenience.

---

# Standing questions after #119

### Given everything that is now formally true, what becomes possible that was not possible before?

An exact negative eigenvalue problem can now be represented by the zero set of one canonical scalar function rather than only by a necessary Schur identity.

### If this contains a clue toward RH, where does it propagate?

Upstream into the metric structure of the projected predecessor block and zero eigenspace; downstream into an explicit real secular scalar, quantitative deformation bounds, parity-resonance control and ultimately exclusion of a global-first-bad finite state.

### What experiment, lemma or reformulation most efficiently tells us whether the clue is real?

First theoremize projected predecessor symmetry/coercivity and the exact explicit scalar bridge. In parallel, test the kernel-coupling statement `Bc ⟂ ker A`. These are the fastest checks of whether the one-dimensional secular reduction has CCM-specific rigidity beyond generic Hermitian block theory.

**RH remains OPEN.**
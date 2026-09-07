# RHRC research leads delta — post PR #122

> **Claim firewall: RH remains OPEN.**
>
> This file records the post-green mathematical consequences of merged PRs #121/#122 and supersedes `RESEARCH_LEADS_POST_119_DELTA.md` for current execution priority. It is a research delta, not a theorem registry. Exact Lean/compiler/CI evidence remains authoritative.

## Exact authority split

```text
live main after #122 = b2d1210902d430f3cdd3c24c2961ab843469b5d6
live main tree = db51419fb7cc8b2e3dbe5cf2e770390086db9862

theorem-state anchor = PR #122 merge b2d1210902d430f3cdd3c24c2961ab843469b5d6
validated theorem head = 9c8154e3ea7a5762f8e65d508dc68bb9246db869
E3-B1 metric control + E4-A1 zero-resonance coupling classification = PROVED / MERGED

control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1
Control v2 / FFBBP v1.6 hardened state = MERGED GREEN CONTROL INFRASTRUCTURE

RH = OPEN
```

The exact #122 theorem head passed the authoritative RHRC/Lean and Permansson workflows before merge.

---

# What became formally true

## PROVED — PR #121: exact explicit cubic Schur bridge

For the canonical safe negative-shift problem, write

```text
A = intrinsicPredecessorBlock
c = intrinsicCubicShellPart
b = intrinsicShellToPredecessor c
R_lam = (A-lam I)^(-1)

S(lam)=<Tc,c>-lam<c,c>-<R_lam b,b>.
```

PR #121 proves

```text
F(lam)=star(S(lam))/<c,c>
```

where `F=cubicSecularScalar` is the exact #119 quotient-coordinate root detector and `<c,c>!=0`.

It also proves exact zero equivalence

```text
S(lam)=0
  <-> F(lam)=0
  <-> canonical trial vector is a genuine eigenmode
  <-> exists a nonzero eigenmode at lam.
```

## PROVED — PR #122: projected metric/resolvent control

On the exact projected predecessor block `A=P_W T|_W`, PR #122 proves:

- exact projection identities for the predecessor block in the ambient successor inner product;
- pairwise symmetry of `A`;
- symmetry of the real shifted block `A-lam I`;
- negative-shift coercivity from predecessor nonnegativity;
- lower/upper resolvent quadratic estimates;
- `(-lam)||R_lam b|| <= ||b||` and quotient norm bound;
- symmetry of the shifted resolvent;
- `Re<R_lam b,b> >= 0` and realness of the resolvent quadratic value;
- denominator-free estimate

  ```text
  (-lam) Re<R_lam b,b> <= ||b||^2;
  ```

- realness of `S(lam)`;
- the unconjugated exact scalar identity

  ```text
  F(lam)=S(lam)/<c,c>;
  ```

- at an exact negative root,

  ```text
  0 <= Re(<Tc,c>-lam<c,c>)
  (-lam) Re(<Tc,c>-lam<c,c>) <= ||b||^2.
  ```

The representation barrier from the post-#119 state is closed.

## PROVED — PR #122: E4-A1 zero-resonance coupling classification

If `z` lies in the kernel of the projected successor predecessor block,

```text
Az=0,
```

then the full successor image lies in the one-dimensional shell. PR #122 proves the exact coefficient identity

```text
<z,b> = star(kappa(Tz)) <c,c>.
```

Therefore

```text
Az=0 -> (<z,b>=0 <-> Tz=0).
```

The quantified theorem proves

```text
b annihilates ker A
  <-> every z in ker A is a genuine successor zero mode.
```

This classifies zero resonance; it does not choose the branch.

## PROVED — ExceptionalZero composition

A hypothetical off-critical-line zeta zero now forces one common global-first-bad finite state carrying:

- an exact negative root of `S` and `F`;
- the real unconjugated bridge between them;
- the #122 root metric constraints;
- the pointwise E4-A1 kernel-coupling equivalence.

**RH remains OPEN.**

---

# What changed

Before #121/#122 the exact root detector was canonical but its explicit inner-product representation had a conjugation/metric gap. Zero resonance was posed only as the unresolved question whether `b` annihilates `ker A`.

After #121/#122:

```text
exact quotient root detector
+ exact explicit Schur formula
+ projected symmetry/coercivity
+ real/nonnegative resolvent quadratic control

=> one exact real scalar root problem on lam<0.
```

And

```text
Az=0
  -> exact shell coefficient for Tz
  -> <z,b>=0 iff Tz=0.
```

The project is no longer blocked on identifying the scalar. It is blocked on the **endpoint/zero-resonance geometry** needed to exclude the remaining negative root.

---

# Upstream implications

## L-122-U1 — split algebraic shift control from negative-shift coercivity

**Research status:** CLEANUP CANDIDATE  
**Formal status:** DERIVED / OPEN REFACTOR

`re_inner_shiftedIntrinsicPredecessorBlock_ge` currently carries `hlam : lam < 0`, but the displayed inequality itself is algebraic from predecessor nonnegativity and the real scalar shift. Negativity is only needed downstream to know `-lam>0` for cancellation/division and a positive coercive floor.

A cleaner upstream API may be:

```text
algebraic shifted quadratic identity/inequality for arbitrary real lam
  -> negative-shift coercive corollary for lam<0.
```

This could reduce assumptions in downstream lemmas without changing the mathematics.

## L-122-U2 — finite symmetric range/kernel interface is now canonical infrastructure

**Research status:** READY / HIGH VALUE  
**Formal status:** DERIVED / OPEN FORMALIZATION

E4-A2 needs the finite-dimensional self-adjoint/symmetric fact specialized to the repository representation:

```text
range A = (ker A)⊥.
```

Because the predecessor subtype uses the ambient successor inner product rather than a nested `InnerProductSpace` instance, Lean engineering should preserve the successful #122 strategy: state the needed orthogonality after explicit coercion instead of forcing a second metric instance.

This is a reusable upstream theorem surface for zero-shift analysis.

---

# Downstream implications

## L-122-D1 — decoupled zero-shift endpoint without A^-1

**Research status:** HIGHEST-PRIORITY THEOREM TARGET  
**Formal status:** DERIVED / OPEN FORMALIZATION

Assume

```text
∀ z, Az=0 -> <z,b>=0.
```

Then symmetry should give

```text
b ∈ range A.
```

Choose `x0` with

```text
A x0=b.
```

The natural zero-shift secular endpoint is then solution-based:

```text
S0 = <Tc,c> - <x0,b>.
```

Two obligations must be theoremized:

1. `<x0,b>` is independent of the chosen solution modulo `ker A` because `b ⟂ ker A`;
2. the negative-shift resolvent scalar converges/identifies with this finite endpoint as `lam -> 0-`, or an algebraic substitute strong enough for root exclusion is proved.

This is the correct zero-shift route. Do not introduce `A^-1`.

## L-122-D2 — resonant zero-eigenspace contribution

**Research status:** HIGH-PRIORITY ALTERNATE BRANCH  
**Formal status:** LEAD / HYPOTHESIS

If there exists

```text
z∈ker A,
<z,b>!=0,
```

then E4-A1 proves `Tz!=0` and `Tz` is a nonzero shell vector.

Finite-dimensional spectral reasoning predicts that `R_lam b` has a zero-eigenspace component proportional to `1/(-lam)`. The exact next target should be a theorem-backed inequality or decomposition strong enough to show the secular resolvent term grows with a definite sign near zero.

Possible target shapes:

```text
(-lam) * Re<R_lam b,b> >= positive kernel-coupling witness
```

or an exact orthogonal-kernel decomposition of the resolvent quadratic value.

A resonant branch may actually **force** a negative secular root rather than exclude one. If so, that would classify such projected-kernel configurations as incompatible with any future positivity theorem and sharply isolate the decoupled branch.

## L-122-D3 — strict secular monotonicity is now unblocked

**Research status:** READY / PARALLEL  
**Formal status:** OPEN

Because `F=S/<c,c>` and `S` is real, a shifted-resolvent identity can now be used directly on the exact root detector.

Expected finite-dimensional spectral behavior:

```text
S'(lam) = -||c||^2 - positive resolvent-square term < 0
```

but calculus is not required if an order/resolvent identity gives the same result.

A successful theorem yields at most one negative root.

**Firewall:** uniqueness is not absence.

## L-122-D4 — #122 supplies the mu=0 base case for the deformation theorem

**Research status:** ACTIVE COMPOSITION  
**Formal status:** PARTLY PROVED / GENERALIZATION OPEN

The root metric theorem

```text
(-lam) Re(<Tc,c>-lam<c,c>) <= ||b||^2
```

is the `mu=0` denominator-free core of the proposed one-step deformation inequality.

The remaining E3-B3 task is no longer speculative ancestry: generalize from predecessor nonnegativity to an independently certified floor `mu`, normalize by `||c||^2`, and derive

```text
d_N(g_N+d_N) <= beta_N^2.
```

---

# Resurrected routes

## L-122-R1 — zero endpoint via range rather than inverse

**Research status:** RESURRECTED / REFRAMED  
**Formal status:** READY

Earlier zero-shift reasoning was blocked by the valid firewall “no `A^-1` at zero.” E4-A1 now supplies the exact condition under which the coupling is orthogonal to the kernel. That makes a range-based endpoint construction viable without weakening the firewall.

The route is resurrected only in this reformulated solution-space form.

## L-122-R2 — parity nullity can constrain the E4 branch rather than replace it

**Research status:** ACTIVE PARALLEL  
**Formal status:** LEAD / OPEN

The rank-at-most-one parity defect and algebraic D-equivalence remain insufficient for Hermitian interlacing, but a shifted-nullity difference theorem may limit how successor zero modes can occur across parity sectors.

After E4-A1, such a theorem could help decide whether “every projected-kernel vector becomes a successor zero mode” is structurally plausible at a global first-bad state.

DR-010 remains dead; none of this uses fitted small commutators, spectral-gap heuristics or eigenvector convergence.

---

# New RH-relevant clues

## L-122-C1 — the obstruction may now be an endpoint dichotomy, not a generic root problem

**Research status:** LEAD / HYPOTHESIS

The combined state suggests a sharper architecture:

```text
S(lam) real and exact on lam<0
S(lam) -> +infinity as lam -> -infinity   [to theoremize if needed]

near 0-:
  resonant branch -> singular resolvent contribution;
  decoupled branch -> finite algebraic endpoint.
```

If E3-C proves strict monotonicity, the entire negative-root problem may reduce to the sign/classification of one zero-shift endpoint in the decoupled branch, while the resonant branch is handled separately.

That is qualitatively stronger than merely knowing a root is unique.

## L-122-C2 — attack the counterexample space by branch classification

**Research status:** ACTIVE CREATIVE LEAD  
**Formal status:** OPEN

Instead of attempting RH directly, classify finite global-first-bad countermodels by:

```text
A>=0
S has a negative root
E4-A1 coupling classification
KKT/cubic/parity constraints
exact N-flow ancestry.
```

Ask whether any such countermodel survives both:

1. the decoupled endpoint conditions, and
2. the resonant kernel conditions.

If one branch becomes impossible and the other reduces to a scalar endpoint inequality, the admissible counterexample space has collapsed substantially even before full RH closure.

## L-122-C3 — zero-resonance coefficient is a canonical shell observable

**Research status:** LEAD  
**Formal status:** PARTLY PROVED

E4-A1 identifies `<z,b>` with the canonical shell coordinate of `Tz` times `<c,c>`. This gives zero resonance a canonical quotient interpretation rather than a basis-dependent coupling coefficient.

That may compose with the cubic parity-defect coordinate from #118, potentially relating successor zero resonance to the exact parity one-channel defect without invoking unitary `D`.

No such cross-parity identity is currently proved.

---

# Falsification checks

## F-122-01 — classification is not decoupling

Do not rewrite

```text
<z,b>=0 <-> Tz=0
```

as

```text
<z,b>=0.
```

The branch outcome remains OPEN.

## F-122-02 — projected kernel is not predecessor-size kernel

`ker A` means the kernel of `P_W T_(N+1)|_W`. It is not theorem-identified with `ker T_N`.

## F-122-03 — A=0, b!=0 generic countermodel

A generic `2x2` Hermitian block with zero predecessor block and nonzero shell coupling can have negative spectrum. Zero resonance is not automatically benign; it may force the very negative root one hopes to exclude.

## F-122-04 — b=0 is not enough

Even perfect kernel decoupling does not exclude a negative root if the shell diagonal itself is negative. Endpoint sign still needs CCM-specific information.

## F-122-05 — monotonicity is not exclusion

Strict monotonicity gives at most one negative root. It does not prove zero roots.

## F-122-06 — no circular endpoint positivity

Do not use positivity of the successor operator to prove the zero-shift endpoint sign at the global first-bad successor. That would assume away the obstruction.

## F-122-07 — no zero inverse

A solution `Ax0=b` in the decoupled branch is not an inverse theorem. Preserve the kernel ambiguity and prove solution-independent scalar quantities explicitly.

## F-122-08 — D remains algebraic

Parity nullity comparison may use rank/kernel algebra. Hermitian interlacing, unitary spectral transport and equal inertia remain unproved.

## F-122-09 — source/normalization firewall unchanged

No #121/#122 theorem changes the canonical/legacy source normalization distinction or the independent source-faithful lane.

## F-122-10 — RH claim firewall

Green metric control + zero-resonance classification != negative-root exclusion != positivity != finite-to-infinite closure != RH.

---

# Highest-leverage next moves

```text
1. E4-A2 decoupled branch:
   prove b ⟂ ker A -> b ∈ range A; build solution-based zero-shift endpoint.

2. E4-A2 resonant branch:
   prove an exact kernel-component/resolvent lower bound or decomposition near lam=0-.

3. E3-C in parallel:
   prove shifted-resolvent identity and strict real secular monotonicity; obtain at most one negative root.

4. E4-B in parallel:
   prove rank-at-most-one shifted-nullity comparison without unitary D.

5. Compose 1-4 into a constrained finite countermodel classification / negative-root exclusion attempt.

6. Generalize #122 mu=0 metric control to E3-B3 only if the resulting deformation theorem still has useful information gain.

7. Keep the source-faithful G1-B1B -> G1-final -> S-NEG -> G23 lane parallel.
```

Mathematical information gain should outrank implementation convenience.

---

# Standing questions after #122

### Given everything that is now formally true, what becomes possible that was not possible before?

The exact negative first-bad spectral obstruction can now be analyzed as a real explicit scalar with theorem-backed metric control, while zero resonance has an exact canonical coupling classification. The next proof no longer needs to guess how the quotient scalar relates to Schur analysis.

### If this contains a clue toward RH, where does that clue propagate?

Upstream into finite symmetric range/kernel structure; downstream into a two-branch zero-shift endpoint analysis, scalar monotonicity/root count, parity-nullity constraints, and ultimately CCM-specific negative-root exclusion.

### What experiment, lemma or reformulation most efficiently tells us whether that clue is real?

The highest-information pair is:

```text
b ⟂ ker A -> b ∈ range A -> finite zero-shift endpoint
```

and its complementary resonant theorem exposing the kernel contribution to `Re<R_lam b,b>`. In parallel, prove monotonicity. Together these tests reveal whether the negative-root problem really collapses to one endpoint sign or whether generic countermodels still survive the full CCM theorem inventory.

**RH remains OPEN.**
# RHRC research leads delta — post PR #125

> **Claim firewall: RH remains OPEN.**
>
> This file records the post-green mathematical consequences of merged PRs #124/#125 and supersedes `RESEARCH_LEADS_POST_122_DELTA.md` for current execution priority. It is a research delta, not a theorem registry. Exact Lean/compiler/CI evidence remains authoritative.

## Exact authority split

```text
live main after #125 = 615437fd5854b4473471d9826b4d4787b2e8e42f
live main tree = 245bba07addba0c5ad85fcf1b1b4218b4432c427

theorem-state anchor = PR #125 merge 615437fd5854b4473471d9826b4d4787b2e8e42f
validated theorem head = 533beb4a42fc96cd43a97e071c6e07e3178872b6
theorem-bearing merged through = PR #125

control-plane anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1

RH = OPEN
```

## What became formally true

### PROVED — PR #124: kernel/range zero-shift dichotomy

For `A=P_W T|_W`, `c=intrinsicCubicShellPart`, `b=Bc`:

```text
range A ⟂ ker A
range A ∩ ker A = {0}
W = ker A ⊕ range A
```

If `b` annihilates `ker A`, then `b ∈ range A`, hence some `x₀` satisfies `A x₀=b`. Any two such solutions have the same quadratic coupling:

```text
Ax=b and Ay=b -> <x,b>=<y,b>.
```

For `z∈ker A` and every safe `lam<0`, #124 also proves

```text
<z,b> = (-lam)<z,R_lam b>
|<z,b>|^2 <= (-lam)||z||^2 Re<R_lam b,b>.
```

A hypothetical off-line zero is therefore reduced at the same global-first-bad state to an exact decoupled/resonant dichotomy.

### PROVED — PR #125: strict zero-shift endpoint

In the decoupled branch define

```text
S0 = <Tc,c> - <x₀,b>,
u0 = -x₀ + c,
Ax₀=b.
```

#125 proves endpoint independence from the chosen preimage, zero predecessor residual for `T u0`, the exact identity

```text
<Tu0,u0> = S0,
```

and the complete-square formula on the predecessor affine fibre. Under predecessor nonnegativity, evaluating at the existing negative secular eigenmode proves

```text
Re S0 < 0.
```

Globally, an off-line zero therefore forces either a strictly negative regular zero-shift endpoint or the exact resonant kernel branch from #124.

## What changed

The old zero-shift obstruction was singularity of `A`. That obstruction is now structurally resolved without defining `A^-1`: the regular branch is represented by a solution-independent scalar, while the complementary branch is an explicit kernel resonance.

The admissible first-bad counterexample space has therefore compressed to:

```text
REGULAR:  Ax₀=b and Re S0<0
or
RESONANT: ∃z∈ker A, <z,b>!=0 with the exact #124 resolvent identity/bound.
```

Neither branch is excluded. RH remains OPEN.

## Upstream implications

### U1 — scalar canonicity is more fundamental than a zero-shift inverse

The #124 solution-independence theorem only needs symmetric range/kernel geometry. A canonical vector or range inverse is unnecessary. Preserve this smaller interface.

### U2 — zero-shift trial vector is an exact constrained critical point

#125 proves the predecessor coordinate of `T u0` vanishes. Because `V=W⊕S` and `dim_C S=1`, the next repository-native theorem should identify the shell response of `T u0` without assuming shell invariance.

## Downstream implications

### D1 — E4-A3 zero-shift shell response

**Formal status: DERIVED / OPEN FORMALIZATION.**

From the proved zero predecessor coordinate of `T u0`, theoremize

```text
T u0 ∈ S.
```

Then use the canonical cubic shell coordinate to obtain a scalar `sigma0` with

```text
T u0 = sigma0 • c
```

and identify `S0` with the corresponding one-dimensional shell response. Do not call `u0` an eigenvector unless `T u0 ∈ span(u0)` is separately proved.

### D2 — E4-A3 exact resonant pole decomposition

**Formal status: LEAD / HYPOTHESIS.**

Using #124's canonical algebraic split `W=ker A⊕range A`, decompose

```text
b=bK+bR
```

and theoremize the exact safe-shift identity

```text
R_lam b = -(1/lam)bK + R_lam bR.
```

This should expose the `1/(-lam)` pole coefficient rather than only a lower bound.

### D3 — E4-A3 branch rigidity

**Formal status: OPEN.**

Compose the strict regular endpoint / resonant pole information with CCM-specific structure:

- parity rank-at-most-one defect;
- parity normal-space / KKT geometry;
- cubic quotient channel;
- predecessor/successor N-flow and first-bad minimality.

The target is branch exclusion or a still smaller countermodel class, not RH by declaration.

### D4 — E3-C remains parallel, but secondary to exclusion

Strict secular monotonicity may give at most one negative root. A hypothetical off-line zero already forces a negative root, so uniqueness alone does not attack existence.

## Resurrected routes

- **Zero shift without inverse:** now PROMOTED through #124/#125 in solution-space form.
- **Parity nullity as a branch discriminator:** still ACTIVE; it may constrain successor zero resonance without unitary `D`.
- **KKT normal-space composition:** newly higher value because `u0` is a constrained critical point on the fixed-shell fibre.

DR-010 remains dead; none of the current route uses fitted small commutators or eigenvector-convergence heuristics.

## New RH-relevant clues

### C1 — regular-versus-pole formulation

The E4-A2 dichotomy appears to be the finite algebraic distinction between a finite regular zero-shift endpoint and an explicit kernel pole of the shifted resolvent.

### C2 — one-dimensional shell response

If the proved zero predecessor residual is compressed to an exact shell coefficient, the negative endpoint becomes a sign restriction on one scalar response rather than merely a negative value in a large space.

### C3 — attack the counterexample space

The next decisive question is whether a finite Hermitian model satisfying all post-#125 CCM constraints still exists. Constructing such a model would falsify an overoptimistic branch-exclusion plan; excluding it would be genuine progress.

## Falsification checks

- Generic Hermitian block systems can have `A>=0` and a negative Schur complement. `Re S0<0` is not itself a contradiction.
- Generic zero resonance can create a negative eigenvalue. Resonance is not automatically impossible.
- `T u0 ∈ S` does not imply `u0` is an eigenvector.
- `ker A` is not the predecessor-size compressed-operator kernel.
- `D` remains algebraic, not unitary/isometric.
- monotonicity/root uniqueness is not root exclusion.
- no finite/fitted deformation tail is an infinite-horizon certificate.
- source normalization and machine claim promotion remain unchanged.

## Highest-leverage next moves

```text
1. E4-A3 ZERO-SHIFT SHELL RESPONSE
   theoremize T u0 ∈ S and the canonical shell coefficient / S0 identity.

2. E4-A3 RESONANT POLE DECOMPOSITION
   theoremize the exact kernel/range decomposition of R_lam b.

3. E4-A3 BRANCH RIGIDITY
   compose 1-2 with parity/KKT/cubic/N-flow and attack finite countermodels.

4. E4-B PARITY SHIFTED-NULLITY in parallel.

5. E3-C RESOLVENT MONOTONICITY in parallel, with the permanent uniqueness != absence firewall.

6. E3-B3 / deformation-budget work only where it adds independent information.

7. Keep the source-faithful G1-B1B -> G1-final -> S-NEG -> G23 lane parallel.
```

## Standing questions after #125

Given everything now formally true, what becomes possible that was not possible before?

If #124/#125 contain an RH-relevant clue, where does the regular endpoint or resonant pole propagate through parity, KKT and N-flow?

What theorem or finite countermodel experiment most efficiently tells us whether that clue is real?

**RH remains OPEN.**
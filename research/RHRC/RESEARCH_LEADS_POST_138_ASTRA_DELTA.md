# RHRC research delta — post-#138 Astra path audit

> **Claim firewall: RH remains OPEN.**
>
> This file records a post-#138 independent research audit and the resulting execution reroute. It is not a Lean theorem, claim promotion, or terminal RH statement.

## Exact authority

```text
live main after merged PR #138 = ebf289bdfdde69020bee0d1571047f155e5de4db
live main tree = d26cd83709437260d0a16630d90c73a93f64c975

theorem-state anchor = PR #137 merge fa2f209a6eb8b4059968e8d61239d80588ca256c
validated theorem head = 64988e142590c82bd0ad43604279ede9a8e85eff
validated theorem tree = e3de4dc0377f0124832822b6f97ab5bbd7718640
RHRC #878 = SUCCESS
Permansson #651 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

PR #138 is documentation/control synchronization only. The latest mathematical increment remains #137.

## Why this delta exists

An independent Astra audit reconstructed the project from roughly PR #132 through merged #138, read the relevant Lean theorem surface, and attacked the current A4b2b route as a mathematical object rather than accepting the roadmap ordering.

The central correction is:

> Under predecessor nonnegativity and a one-dimensional shell, universal `q_c >= 0` plus `Delta(w) >= 0` for every predecessor vector is not merely close to successor positivity; it is the full two-dimensional compression formulation of successor positivity.

Therefore universal A4b2b remains a valid sufficient closing theorem, but it is not presently a smaller RH subproblem. The next move should first remove the avoidable singular/resonant branch without proving positivity.

## What remains PROVED

The theorem inventory is unchanged.

### PROVED — global reduction through #137

A hypothetical off-line zeta zero forces a finite global-first-bad canonical state with both predecessor parity forms nonnegative and an exact safe negative explicit Schur root. PR #137 then proves failure of `canonicalOneStepDomination`, equivalently

```text
q_c < 0
OR
exists w, Delta(w) < 0.
```

### PROVED — absolute energy and source pairing

PR #136 gives scalar-sensitive canonical self-energy and the exact pole/arch/scalar/prime channel decomposition. PR #137 gives the exact complex source pairing, predecessor energy, shell coupling, and one-step determinant.

### PROVED — conditional domination consequences

If `canonicalOneStepDomination` holds, then the shell coupling annihilates `ker A`, lies in `range A`, a zero-shift preimage exists, `Re S0 >= 0`, and no safe negative explicit Schur root exists.

No theorem proves domination itself.

## Post-#138 DERIVED state

The following statements are mathematical consequences identified in the external audit. They are **DERIVED**, not newly Lean-locked.

### DERIVED — universal determinant certificate is successor positivity

Let the successor space split orthogonally as `V = W ⊕ C c`, with predecessor block `A >= 0`, shell energy `q_c`, shell coupling functional `B(w)`, and

```text
Delta(w) = q_c*q_A(w) - |B(w)|^2.
```

Then

```text
q_c >= 0 AND forall w, Delta(w) >= 0
```

is equivalent to nonnegativity of the full one-step successor quadratic form.

**Research consequence:** proving the universal determinant cone without an independent arithmetic mechanism is not a reduction of the remaining RH positivity obstruction.

### DERIVED — exact regular/resonant classification

Let `k = P_(ker A) b`.

```text
RESONANT: k != 0.
REGULAR:  k = 0, equivalently b in range A.
```

In the regular branch choose `x0` with `A x0 = b`. Then

```text
S0 = q_c - q_A(x0).
```

The value is independent of the chosen preimage modulo `ker A`.

If `A` is positive definite, the preimage is unique:

```text
x0 = A^-1 b
u0 = c - A^-1 b.
```

The remaining bad regular state is therefore a single scalar statement

```text
Ecanonical(u0) = Re S0 < 0.
```

### DERIVED — canonical resonant determinant witness

For `k = P_(ker A)b`,

```text
Delta(k) = -||k||^4.
```

Thus resonance itself supplies an explicit negative determinant witness. This sharpens the #137 existential countercertificate but does not exclude resonance.

### DERIVED — root-selected determinant witness

At a safe negative explicit root `lambda < 0`, put

```text
w_lambda = (A - lambda I)^-1 b
r_lambda = q_A(w_lambda)
n_lambda = ||w_lambda||^2.
```

The audit derives

```text
Delta(w_lambda)
  = lambda*r_lambda*(rho + n_lambda)
    - lambda^2*n_lambda^2.
```

If `b != 0` this is strictly negative; if `b = 0`, the shell-energy branch is negative instead. This is generic block algebra and witness selection, not arithmetic exclusion.

### DERIVED / external exact-check — correction-vector proportionality

The audit reports the exact geometric identity

```text
d = -(6/(2*N-1)) * a
```

for the two odd predecessor correction vectors, checked by exact rational arithmetic for `K = 2,...,30` and supported by an elementary power-sum derivation.

This is **not yet Lean theorem authority**. If formalized, it eliminates any route requiring those correction vectors to be independent.

### DERIVED — first variation of the regular Schur energy

For a differentiable regular matrix family with fixed carrier/shell and minimizing trial `u0 = c - A^-1 b`, stationarity gives

```text
dS0/dt = <u0, M'(t) u0>.
```

For a relative perturbation of one prime weight this becomes the corresponding negative prime-atom energy contribution. This gives a precise sensitivity observable for discovery work.

## Rerouted critical path

The immediate frontier is now **A4R regular-aperture selection**, upgraded from fallback to primary reduction.

Desired chain:

```text
off-line zeta zero
  -> strict finite canonical negative witness                      PROVED
  -> move to arbitrarily nearby aperture while preserving negativity  OPEN
  -> avoid finitely many predecessor singularities in both parities   OPEN
  -> reselect global first-bad state at the new aperture              OPEN
  -> both predecessor parity blocks positive definite                 OPEN
  -> unique regular zero-shift preimage x0 = A^-1 b                   DERIVED from finite linear algebra
  -> Ecanonical(c - A^-1 b) = Re S0 < 0                               PROVED ingredients / wrapper OPEN
  -> independent arithmetic proof Ecanonical(c - A^-1 b) >= 0        OPEN / decisive
  -> contradiction                                                     DERIVED
  -> no off-line zero                                                   DERIVED from existing reduction
  -> explicit Mathlib RiemannHypothesis wrapper                         OPEN to compile/audit
```

Regularity is useful because it removes a branch without assuming any sign for the successor.

## LEAD — logarithmic determinant nonidentity

The candidate mechanism is to freeze the finite prime cutoff `Q` and expose the exact scalar normalization in the fixed carrier:

```text
M_Q(L) = -log(L) I + B_Q(L).
```

Set `L = exp(z)`. The proposed analytic continuation has the form

```text
M_Q(exp z) = -z I + Bhat_Q(z)
```

with the remainder periodic under `z -> z + 2*pi*i`.

If `det(Bhat_Q(z) - z I)` vanished identically, periodicity would make one fixed `d x d` characteristic polynomial vanish at `d+1` distinct points `z, z+2*pi*i, ..., z+2*pi*i*d`, impossible.

This is a **LEAD / HYPOTHESIS** until the production canonical source satisfies all required analytic and compression obligations.

Required proof gates:

1. exact `-log L` scalar coefficient after the actual parity/BF compression;
2. frozen-cutoff real analyticity/holomorphy on the needed domain;
3. physical cutoff-threshold continuity, including entering prime-power atoms;
4. fixed carrier bases independent of `L`, or exact Gram corrections if not;
5. simultaneous avoidance for finitely many sizes and both parities;
6. preserve the strict negative witness by continuity first;
7. **reselect first-bad after perturbation** rather than assuming the old least-bad index persists;
8. identify the intrinsic projected predecessor with the relevant predecessor compression.

Failure of any of these gates narrows or kills this A4R implementation, not RH.

## What happens after regularity

Regularity does not prove positivity. It reduces the forced bad state to the scalar

```text
S0 = q_c - <b, A^-1 b>
```

in the exact canonical normalization.

The highest-closing-leverage theorem would be an independent source-specific bound

```text
<b, A^-1 b> <= q_c
```

or an equivalent exact paired-channel remainder proving

```text
Ecanonical(c - A^-1 b) >= 0
```

on the forced regular trial.

A proof that defines an auxiliary positive form whose positivity is equivalent to the desired inequality is circular and should be rejected.

## Falsification results to preserve

### DERIVED / external symbolic result — atomwise determinant positivity fails

The audit reports that the first nonzero two-vector determinant coefficient of an elementary source atom is negative. On the boundary-flat parity sectors the leading orders occur at `omega^18` in odd parity and `omega^22` in even parity for the tested predecessor/shell fixtures.

Therefore the old `omega^7 / omega^9` cancellation lead does **not** support a positive atom-by-atom determinant/SOS proof.

This does not determine the sign of the full canonical source determinant, where mixed pole/arch/scalar/prime terms may cancel.

### EXPERIMENTAL SIGNAL — canonical Schur cancellation is extremely sharp

The audit reports sampled canonical cases with positive predecessors/successors, including an even `L=3, K=6` regular endpoint near

```text
S0 ~= 4.91225958747865e-10
```

while the ratio of summed absolute channel magnitudes to the final endpoint is approximately

```text
6.4583e20.
```

This is not interval-certified repository evidence. It is a warning that independent channel majorants may be far too lossy.

### EXPERIMENTAL SIGNAL — exact prime coefficients matter

At `L=2, K=3`, the audit reports that a relative `1e-8` perturbation of the prime-2 coefficient can make one successor negative while both predecessors and shell energy remain positive. A consistent perturbation of the available powers `2,4` shows the same qualitative effect.

These are modified sources, not canonical zeta counterexamples. They falsify only arguments that use positivity of weights, finite support, parity, or channel structure without the exact arithmetic coefficients.

## Resurrected and demoted routes

### PROMOTED — A4R regular-aperture selection

Previously fallback. Now highest plausible unconditional reduction because it can eliminate resonance by witness selection without proving successor positivity.

### DEFERRED — universal A4b2b domination

Still a valid sufficient closing theorem. It is no longer the immediate frontier because, under the current one-dimensional-shell hypotheses, its universal content is the successor positivity problem itself.

Promote it again immediately if a genuinely independent canonical arithmetic mechanism is found.

### OPEN ALTERNATIVE — pole-neutral finite approximation

Preserving the original pole-killing constraints through finite approximation could shrink the forced carrier further. The audit identifies a promising fixed-moment formulation after a diagonal change of variables. The required approximation and revised shell theory are not proved.

### STILL LOW PRIORITY

Shifted-nullity, secular monotonicity, deformation, and cross-parity composition remain available but have not gained an independent exclusion mechanism. Root uniqueness remains weaker than root absence.

## Highest-leverage next theorem

Target:

> Every finite canonical negative witness can be moved to an arbitrarily nearby aperture and reselected as a global first-bad witness with both predecessor parity blocks positive definite.

A suitable internal theorem family should first prove simultaneous finite-block injectivity on a dense set of positive apertures and then package the off-line-zero witness selection.

The theorem must not assume predecessor positive definiteness, regular preimages, successor positivity, determinant sign, or RH.

## Highest-leverage experiment after that

Analyze the **full regular minimizing-trial Schur remainder**, not generic eigenvalue signs:

```text
u0 = c - A^-1 b
S0 = Ecanonical(u0)
```

Compute and eventually interval-certify:

- pole contribution;
- reduced arch diagonal/off-diagonal contribution;
- scalar correction;
- finite prime contribution;
- `S0` itself;
- `r/q_c`;
- prime-coefficient sensitivities from the first-variation identity.

The scientific question is whether exact prime/archimedean/scalar cancellation admits a uniform independently controlled remainder.

## Falsification checks for the reroute

- verify the exact production `-log L` coefficient; fail if a basis/Gram factor is missing;
- do not assume the physical prime cutoff is frozen globally;
- test continuity at prime and prime-power entry thresholds;
- handle zero-dimensional carriers explicitly;
- require both parities and every predecessor size through the selected finite horizon;
- preserve negativity before reselecting first-bad;
- retain generic regular negative examples as negative controls so the theorem does not silently prove positivity;
- do not promote external exact checks or high-precision numerics to PROVED status;
- do not treat a regular first-bad witness as a contradiction by itself.

## Standing questions

**What became possible after #137/#138 that was not possible at #132?**  
The forced RH counterexample class can now be expressed in absolute source energy and exact one-step pairing coordinates. That makes it possible to separate removable singular geometry from the genuinely arithmetic regular Schur sign.

**Where does the RH clue propagate?**  
Upstream to the exact scalar normalization and aperture dependence; downstream to one minimizing-trial canonical energy.

**What smallest fact would most change our belief in the route?**  
First, whether the log-lift really gives dense simultaneous regular apertures for the production matrices. After that, whether the exact prime/arch/scalar cancellation on `u0` admits a rigorously controlled positive remainder.

## Status summary

```text
PROVED:
  theorem authority through #137
  off-line zero -> finite first-bad sign-failure countercertificate

DERIVED:
  universal determinant cone = successor positivity under A>=0 and dim shell=1
  regular/resonant Schur classification
  Delta(P_kerA b) = -||P_kerA b||^4
  root-selected determinant identity

LEAD:
  logarithmic determinant nonidentity / dense regular-aperture selection
  independent paired-channel regular Schur bound
  pole-neutral refined carrier

EXPERIMENTAL SIGNAL:
  sharp canonical Schur cancellation
  prime-weight sensitivity
  finite sampled positivity

OPEN:
  regular-aperture theorem
  regular canonical Schur-energy nonnegativity
  negative-root exclusion
  terminal Mathlib RH wrapper
  RH
```

**RH remains OPEN.**
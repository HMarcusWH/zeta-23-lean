# RHRC post-green research delta after PR #129

> **Claim firewall: RH remains OPEN.**
>
> This document is the current incremental research authority after merged green PRs #127/#128/#129. It supersedes older post-green deltas for current priority where they conflict, while leaving those older files historical.

## Exact authority checked

```text
validated theorem head = 440be3e5b6bf05e94ae2c65b1704d52d20acc9af
validated theorem tree = 2f042a3b0b3313e7c67d627a58a32d579d4e7ff7
merged main = e1192857afed9f68fa4a13143ce690b62191b997
merged main tree = 2f042a3b0b3313e7c67d627a58a32d579d4e7ff7
PR = #129
RHRC #838 = SUCCESS
Permansson #611 = SUCCESS
control-plane semantic anchor = #117
RH = OPEN
```

The exact #129 theorem head and merged main share the same theorem tree. Compiler/CI evidence is authoritative for formal validity.

---

# What became formally true

## PROVED — PR #127: canonical zero-shift shell response

For the decoupled zero-shift branch with `Ax0=b` and

```text
u0 = -x0 + c,
```

Lean proves for the specific trial image:

```text
T u0 = shellPart(T u0),
sigma0 • c = T u0,
S0 = star(sigma0) * <c,c>.
```

This is not shell invariance and not an eigenvector theorem.

The conjugation in the final identity is essential under Mathlib's complex-inner-product orientation.

## PROVED — PR #128: signed response and canonical resonant pole

The regular branch is sharpened at the forced negative explicit root:

```text
Re sigma0 < 0.
```

On the predecessor block, Lean theoremizes the canonical kernel coordinate and proves that it vanishes exactly on `range A`. For the safe shifted resolvent:

```text
(-lam) • K(R_lam b) = K(b).
```

For the canonical cubic coupling define

```text
k = K(b).
```

Then:

```text
REGULAR / DECOUPLED: k = 0
RESONANT:            k != 0
                     K(R_lam b)=(-lam)^(-1) • k   for lam<0.
```

The denominator-free identity is the primary theorem; the divided form is a corollary.

## PROVED — PR #129: source-explicit cubic defect

`SourceExplicitCubicDefect.lean` defines the orthogonalized quadratic normal

```text
n2 = d^2 - projection of d^2 onto the constant normal direction
```

and the canonical source moment

```text
evenQuadraticSourceMoment L K v
  = <n2, canonicalSourceMatrix(L,K) v>/<n2,n2>.
```

The main theorem

```text
cubicDefectFunctional_eq_evenQuadraticSourceMoment
```

proves, for `K>=2`, that the cubic parity-defect coefficient is exactly this actual canonical-source moment.

No sign or nonzeroness on a particular trial/eigenvector is proved.

## PROVED — PR #129: exact cross-parity secular transfer

The compiler-audited theorem surface includes:

```text
intrinsicCubicQuotientCoordinate_evenIndex
cubicSecularResidual_eq_scalar_smul_intrinsicCubicShellPart
cubicSecularTrialVector_odd_eq_evenIndex_sub_resolvent_forcing
cubicSecularScalar_odd_eq_alpha_mul_even_add_gamma_mul_defect
crossParitySecularGamma_eq_trial_cubic_overlap_div
cubicSecularScalar_crossParity_source_transfer
cubicSecularScalar_odd_eq_overlap_mul_source_of_even_root
```

At the mathematical level, for the same `L,N,lam<0` and both predecessor parities nonnegative:

```text
F_- = alpha * F_+ + Gamma * sourceMoment(u_+).
```

The D-transported even cubic shell is theoremized with its exact predecessor-plus-shell decomposition; the proof retains the predecessor correction term and never treats D as unitary/isometric. No nonzeroness of that predecessor correction is claimed.

`Gamma` is identified with an exact odd trial / full odd cubic-generator overlap divided by `<c_-,c_->`.

At an even root:

```text
F_+ = 0
=> F_- = overlap * sourceMoment(u_+).
```

At an odd root the full balance is retained. No division by `alpha`, `Gamma`, the overlap or the source moment occurs.

## PROVED — PR #129: global off-line-zero source-explicit certificate

The theorem

```text
exists_globalFirstBad_crossParitySecularTransfer_of_offLine_zero
```

composes the transfer with the already-proved global first-bad reduction. Any hypothetical off-line zeta zero therefore forces one finite state with:

- positive aperture;
- a least globally bad successor size;
- both predecessor parities nonnegative;
- a safe negative explicit Schur root in one parity;
- the complete source-explicit cross-parity certificate at the same state.

This is not branch exclusion or RH.

---

# What changed

The important change is not merely that three more lemmas became available. The mathematical bottleneck moved.

Before #127/#128 the project still needed to expose the regular shell response and resonant kernel pole. Those are now theorem-backed.

Before #129 the parity defect was still an abstract cubic coefficient. It is now literally an explicit moment of the actual canonical source matrix.

Therefore the route has crossed from

```text
generic finite block / parity rigidity
```

into

```text
actual canonical-source-value rigidity.
```

That distinction matters because the generic structural package has now been adversarially tested and found insufficient.

The old E4-A3 agenda is consumed:

```text
A3a shell response              PROVED / #127
A3b resonant pole               PROVED / #128
A3c exact parity/source transfer PROVED / #129
```

The next semantic layer should be E4-A4 canonical-source branch exclusion.

---

# Upstream implications

## 1. `cubicDefectFunctional` should now be treated as a source observable

Before #129 it was natural to think of the cubic coefficient as an algebraic defect coordinate. The theorem

```text
cubicDefectFunctional = evenQuadraticSourceMoment
```

shows that the same object is directly readable from the canonical source formula.

This suggests an upstream abstraction opportunity: source-sensitive lemmas should be stated in terms of `evenQuadraticSourceMoment` when the source formula is doing work, with the algebraic cubic functional recovered by the exact theorem when needed.

## 2. The centered quadratic normal is now a canonical interface

`centeredQuadraticNormal` isolates the `d^2` normal channel after removing the constant component. Any future source decomposition should reuse this vector rather than re-derive coefficient comparisons from existential KKT decompositions.

Potential upstream theorem targets:

```text
sourceMoment = prime contribution + arch contribution + diagonal contribution
```

or a smaller exact identity if some channels vanish against `n2`.

## 3. The D-transport correction must be retained unless separately proved zero

**PROVED:** #129 theoremizes the exact decomposition

```text
D c_+ = dW + c_-
```

where `dW` is the odd predecessor part. Lean does **not** prove `dW != 0`; in particular the allowed boundary case `N=1` can have zero predecessor correction.

**EXPERIMENTAL SIGNAL:** the exact-rational discovery checks found `dW` nonzero generically in the tested models, and dropping the predecessor correction caused 140 transfer/reconstruction checks to fail.

Therefore future parity simplifications should preserve the predecessor term by default, but must not promote its nonzeroness without a separately scoped theorem.

## 4. The canonical matrix normalization is now even more central

The #129 source moment uses

```text
canonicalSourceMatrix
```

not the legacy identity-shifted `finiteMatrix`.

Because the active observable is sign-sensitive and source-explicit, the old normalization firewall is now directly on the critical path rather than merely background hygiene.

---

# Downstream implications

## 1. The next contradiction can be source-local rather than global

The existing off-line-zero theorem already produces an exact finite first-bad state. Therefore a theorem that universally excludes the two actual canonical branches at that finite state would immediately contradict every hypothetical off-line zero in the project carrier.

No new finite-to-infinite limit theorem is required for that implication: the reduction starts from an arbitrary off-line zero and ends at the finite obstruction.

A separate explicit bridge to the final Mathlib `RiemannHypothesis` statement would still be required for terminal closure.

## 2. Even-root analysis factorizes cleanly

At an even forced root,

```text
F_- = overlap * sourceMoment(u_+).
```

Thus same-lambda odd rootedness is equivalent to the product vanishing. This gives two concrete subcases to investigate:

```text
overlap = 0
or
sourceMoment(u_+) = 0.
```

No theorem yet says either factor is nonzero. But this factorization is much sharper than a generic parity comparison.

## 3. Odd-root analysis retains a balance law

At an odd forced root,

```text
0 = alpha * F_+ + Gamma * sourceMoment(u_+).
```

This may be more useful than trying to force the root parity to be even. The route should not assume a preferred parity unless separately proved.

## 4. Regular and resonant branches can now be attacked with the same source observable

The #129 source moment is available independently of which #128 branch occurs. That creates a shared downstream interface:

```text
branch data + sourceMoment + cross-parity transfer.
```

This is the first point where both branches can be tested against one actual source formula without reducing them to the same generic Schur mechanism.

---

# Resurrected routes

## Source-faithful G1-B1B / G1-final lane — partially resurrected as a cross-check

Earlier source-interface work was kept parallel because the shortest internal F1 route did not require full ambient source reconstruction.

PR #129 changes the situation: source values now sit directly inside the active first-bad parity equation. Therefore source-faithful objects such as the multiplicative/Haar presentation, `PsiSharp`, or other canonical-source decompositions may become useful again **if** they give an exact formula for the source moment or a sign-relevant decomposition.

This is a changed-premise resurrection: the source lane is no longer being asked to replace the internal route; it may now feed a specific scalar already theoremized inside that route.

## Displacement/prolate lane — remains supporting, not terminal

Exact displacement structure remains useful for source algebra, but post-#128 diagonal countermodels show it cannot be the terminal contradiction by itself.

The route is not dead; its role is narrower. It must combine with actual source values not preserved by arbitrary diagonal perturbations.

---

# New RH-relevant clues

## LEAD / HYPOTHESIS A — exact source-channel decomposition of the quadratic normal moment

Assume #129 matters more than it first appears. The most plausible reason is that the orthogonalized `d^2` moment kills or simplifies large parts of the source formula.

Fast question:

```text
What survives when the actual canonicalSourceMatrix formula is paired with n2 and u_+?
```

Possible outcomes worth theoremizing:

- constant/normalization terms vanish exactly;
- an archimedean piece has a fixed sign;
- prime contributions collapse to a weighted centered second moment;
- the canonical diagonal contributes a term absent from generic countermodels;
- the full moment factors through an already-controlled quantity.

Do not guess the sign before deriving the exact formula.

## LEAD / HYPOTHESIS B — regular branch may be excluded by a source Cauchy/block inequality

A transparent sufficient condition is a one-step block-positivity certificate of the form

```text
q_c >= 0
|<w,b>|^2 <= q_c q_A(w).
```

For `w=x0` this would contradict the strict negative regular endpoint. But this is essentially the desired one-step positivity theorem if merely assumed.

The real lead is narrower:

> can the exact source decomposition of `sourceMoment(u_+)`, together with #129 parity transfer, derive a special case of that inequality only on the canonical first-bad trial data?

That would be materially weaker than proving the whole successor block positive and therefore potentially reachable.

## LEAD / HYPOTHESIS C — resonance may force a source-moment or overlap degeneracy

In the resonant branch `k!=0` and the kernel coordinate of the shifted resolvent has an exact pole. The parity transfer might force one of:

```text
sourceMoment(u_+) = 0
overlap = 0
Gamma = 0
```

or an exact relation incompatible with `k!=0` once the production source formula is expanded.

This is speculative and should be attacked by explicit finite examples before formalization.

## LEAD / HYPOTHESIS D — attack the counterexample space rather than RH directly

The accumulated theorem inventory says every off-line zero must generate a very specific finite state. A productive objective is therefore:

```text
classify all canonicalSourceMatrix first-bad states satisfying #129.
```

Even if immediate exclusion fails, proving that such states must satisfy increasingly rigid moment/overlap identities shrinks the admissible counterexample space and may expose the decisive obstruction.

---

# Falsification checks

## Generic regular countermodel

```text
T = [[1,1],[1,0]]
A = [1]
b = [1]
u0 = (-1,1)
T u0 = (0,-1)
S0 = -1.
```

This shows a nonnegative predecessor and negative pure-shell zero-shift response are generically compatible.

## Generic resonant countermodel

```text
T = [[0,1],[1,0]]
A = [0]
b = [1].
```

This has exact zero resonance and negative eigenvalue `-1`.

## Centered-grid structural countermodels

On the actual radius-3 centered grid with actual boundary-flat parity spaces and generic reversal-symmetric diagonal `diag(q_|d|)`, the discovery pass found:

```text
q=(1,1,1,-10): both predecessors positive; both regular responses negative
q=(0,1,4,-10): odd successor negative; even successor positive
q=(0,1,-4,0): genuine odd resonance; both successor kernels zero
```

These falsify generic parity-transfer, generic resonance-nullity and generic first-bad/KKT/rank-one exclusion claims.

## Displacement-preserving diagonal perturbations

Because diagonal perturbations commute with the centered index operator, they preserve the displacement commutator while changing absolute spectral signs. Therefore displacement identity alone is insufficient.

## Exact rational transfer regression

Recorded discovery checks:

```text
37 parameter cases × 5 negative shifts = 185 exact transfer/reconstruction/overlap checks passed
74 exact KKT source-moment coefficient checks passed
140 checks failed when the predecessor correction in D c+ was omitted
```

These are **EXPERIMENTAL SIGNAL**, not proof.

## Fast adversarial tests for every A4 theorem candidate

Before formalizing:

1. test `N=1` boundary behavior;
2. test sourceMoment=0;
3. test overlap=0;
4. test `Gamma=0`;
5. test `alpha=0`;
6. test arbitrary reversal-symmetric diagonal perturbations;
7. verify no use of D-unitarity/isometry;
8. verify no division by an unproved factor;
9. verify the theorem fails, or uses an explicit extra source hypothesis, on the known generic fixtures;
10. check that no assumption is already RH-equivalent or silently implies successor positivity.

---

# Highest-leverage next moves

## 1. E4-A4a — theoremize the exact canonical source-moment decomposition

Highest information gain. Work directly from the repository definition of `canonicalSourceMatrix` and prove the cleanest exact formula for

```text
evenQuadraticSourceMoment L (N+1) uPlus.
```

Do not start with a positivity inequality.

## 2. Build a source-faithful executable oracle for that exact formula

Before a large Lean proof, evaluate the exact source decomposition on legal small-N states and on controlled perturbations. The objective is falsification of candidate sign/nonvanishing statements, not curve fitting.

## 3. Split regular and resonant exclusion theorem design

Do not force one contradiction mechanism onto both branches.

Regular branch input:

```text
k=0, Re sigma0<0, parity transfer, sourceMoment.
```

Resonant branch input:

```text
k!=0, exact kernel pole, parity transfer, sourceMoment.
```

## 4. Reuse the #129 overlap theorem before inventing a new scalar

`Gamma` already has a metric overlap representation. Any new source theorem should first ask whether this overlap can be related to the same source moment or to the kernel coordinate.

## 5. Keep E4-B/E3-C/E3-B3 subordinate to information gain

Advance them only if they constrain the source-specific branch problem. Root uniqueness or another generic metric bound is not enough by itself.

---

# Standing questions after #129

> Given everything that is now formally true, what becomes possible that was not possible before?

We can now ask the actual canonical source formula, at one exact global-first-bad state, to decide between explicit parity/root constraints. Before #129 the source coefficient was not exposed in the secular transfer.

> If this contains a clue toward RH, where does that clue propagate upstream or downstream through the existing mathematics?

Upstream it points to `canonicalSourceMatrix` decomposition and source-normalization identities. Downstream it feeds both regular and resonant branch exclusion and, if successful, the already-proved off-line-zero reduction.

> What experiment, lemma, reformulation, or connection would most efficiently tell us whether that clue is real?

Derive the exact formula for the #129 quadratic source moment and immediately falsify candidate sign/nonvanishing properties on small canonical states and diagonal perturbation controls. This directly tests whether actual source values add information beyond the generic countermodels.

---

# Claim firewall

**PROVED:** exact statements above through PR #129 only.

**DERIVED:** straightforward consequences such as even-root product factorization implications, not separately promoted unless theorem-backed at the exact desired statement.

**LEAD / HYPOTHESIS:** source-channel sign/nonvanishing/exclusion mechanisms.

**EXPERIMENTAL SIGNAL:** structural countermodels and exact-rational discovery checks.

**OPEN:** exclusion of the regular branch; exclusion of the resonant branch; canonical negative-root exclusion; explicit terminal RH bridge; RH.

**RH remains OPEN.**

# RHRC formal audit — theorem authority through PR #146; parameter-holomorphy frontier

> **RH remains OPEN.**

## Current authority split

```text
live main after merged PR #146 = f2999d12e29d61debce130e83491ac3df410b0c2
live main tree = fe76581d445569cb838cb4df7bf50703aa34f5cc

theorem-state anchor = PR #146 merge f2999d12e29d61debce130e83491ac3df410b0c2
validated theorem head = a25d238478f7b19072c5364486b8f3f994bf6b79
validated theorem tree = fe76581d445569cb838cb4df7bf50703aa34f5cc
RHRC #922 / run 34600323163 = SUCCESS
Permansson #695 / run 34600323144 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

Live GitHub head + exact compiler/CI evidence outrank this prose.

## Exact theorem-state progression

### PR #134 — zero-shift source transport

**PROVED:** denominator-free whole-kernel source transport, direct zero-shift cross-parity transfer, exact zero-shift `Gamma` overlap formula, and `Gamma0*mu(z)=0` under both preimage hypotheses.

### PR #136 — absolute canonical source energy

**PROVED:** scalar-sensitive `matrixRealEnergy`, identity-shift sensitivity, exact prime/arch/scalar source-energy decomposition, cubic-shell energy, regular zero-shift trial energy `= Re S0`, and negative explicit Schur root -> negative canonical trial energy.

### PR #137 — canonical one-step determinant reduction

**PROVED:** exact complex source pairing, predecessor energy, shell coupling and

```text
Delta(w)=q_c*q_A(w)-|<w,b>|^2.
```

Also PROVED: conditional domination sufficiency, kernel/range zero-shift consequences, `Re S0>=0` under domination plus predecessor nonnegativity, no safe negative explicit Schur root under domination, exact domination-failure disjunction, and the global off-line-zero sign-failure countercertificate.

### PR #140 — aperture freedom and regularity scaffold

**PROVED:** every sufficiently large aperture carries a finite boundary-flat canonical negative witness if an off-line zero exists; `IntrinsicPredecessorRegular <-> injective intrinsicPredecessorBlock`; a regular predecessor gives a unique cubic zero-shift preimage; frozen prime-cell equality and threshold source-atom vanishing hold; and the real-axis scalar extraction has exact `-log(L)` coefficient.

### PR #142 — fixed-cell continuity and witness persistence

**PROVED:** on each physical cutoff cell `I_Q=(log Q,log(Q+1))` with `Q>=1`, entries of the actual production `canonicalSourceMatrix` and every fixed-vector real canonical quadratic energy are continuous. A strict negative witness therefore persists on an open in-cell neighborhood with the same finite size and same vector.

### PR #144 — frozen production and logarithmic-cover scaffold

**PROVED:** the exact frozen canonical source agrees with the actual production source on its physical cutoff cell.

**PROVED:** the exact ambient scalar split

```text
frozen source = -log(L) * I + frozen remainder
```

survives parity compression and the actual intrinsic predecessor projection with coefficient exactly `-1`.

**PROVED:** the exact complex frozen source/intrinsic-predecessor remainder has the correct positive-real bridge.

**PROVED:** the logarithmic-cover objects satisfy

```text
lifted remainder(z+2*pi*i)=lifted remainder(z)
lifted block(z+2*pi*i)=lifted block(z)-(2*pi*i)I
```

and evaluating the lifted block at `z=log L` on a physical cutoff cell gives the actual production `intrinsicPredecessorBlock`.

These are exact algebraic/production/log-cover theorems. They do not prove the remainder is holomorphic in the parameter.

### PR #145 — local removable scalar analyticity

**PROVED:** the removable scalar factor has value `2` at zero, `complexArchExpSlope` is nonzero on a genuine neighborhood of zero, the removable factor is analytic at zero, the value lies in the principal-log slit plane, and the principal-log scalar remainder is analytic at zero.

This is deliberately local. The divided exponential slope has nonzero zeros at `2*pi*i*k`, `k!=0`, so there is no global-entire quotient claim.

### PR #146 — production bridge for the removable scalar layer

**PROVED:** for `z!=0`, the removable scalar factor is exactly `complexApertureScalarFactor`.

**PROVED:** for `z!=0`, the removable scalar remainder is exactly `complexApertureScalarRemainder`.

**PROVED:** on `L>0`, both repaired objects are locked back to the exact positive-real production formulas.

The proof explicitly handles the case `exp z - 1 = 0`; it does not assume global denominator nonvanishing.

## Exact validation evidence for #146

Validated theorem head:

```text
a25d238478f7b19072c5364486b8f3f994bf6b79
```

Validated theorem tree:

```text
fe76581d445569cb838cb4df7bf50703aa34f5cc
```

Merged main commit:

```text
f2999d12e29d61debce130e83491ac3df410b0c2
```

Merged main has the same theorem tree as the validated PR head.

RHRC run #922 (`34600323163`) succeeded, including `python-rhrc`, `r003-normalization-audit`, aggregate `lake build Zeta23.CCM`, aggregate `lake build Zeta23.ExceptionalZero`, and the forbidden placeholder/project-axiom scan. Permansson run #695 (`34600323144`) also succeeded.

## What is not yet proved

No theorem currently proves:

```text
parameter holomorphy of complexAlphaCore
parameter holomorphy of complexBetaCore
parameter holomorphy of complexGammaCore
holomorphy of complexFrozenCanonicalSourceRemainder
holomorphy of complexFrozenIntrinsicPredecessorRemainder
holomorphy/nonidentity of the relevant determinant
dense regular apertures on the physical cutoff cell
production cell-minimal regular first-bad selection
regular canonical Schur-energy nonnegativity
negative-root exclusion
RH
```

## Active analytic theorem

The smallest current obstruction is genuine parameter-integral holomorphy.

The exact production/log-cover family is already present; the proof must now establish actual complex differentiability rather than infer it from structural identities.

Preferred prototype:

```text
complexBetaCore
```

with a proof architecture of:

```text
fixed integration interval
+ local denominator nonvanishing/control
+ pointwise differentiability in the complex aperture parameter
+ locally uniform integrable majorant
-> differentiate under the integral
-> Analytic/Holomorphic parameter dependence.
```

Then reuse the pattern for `complexAlphaCore` and `complexGammaCore`, assemble source holomorphy, and push through the fixed projections to the intrinsic predecessor remainder.

## Translation/deck-law falsification

The exact #144 deck law does not imply holomorphy.

The generic function

```text
F(z)=-z+Re z
```

has affine imaginary-translation behavior of the same structural kind while failing complex differentiability. Therefore any proposed proof that substitutes deck-periodicity or a translation identity for genuine analytic control is invalid.

This negative control is documented in `research/RHRC/countermodels/POST_146_TRANSLATION_NOT_HOLOMORPHY_COUNTERMODEL_2026_09_11.md`.

## Candidate determinant nonidentity argument

Only after genuine holomorphy is established should the #144 lifted structure become load-bearing:

```text
Ahat(z)=-z I + R(exp z)
R(exp(z+2*pi*i))=R(exp z).
```

If `det Ahat` vanished identically, the intended finite-dimensional spectral/root-counting mechanism would force one fixed finite operator to support too many distinct scalar shifts/eigenvalues. This remains a **LEAD / HYPOTHESIS**, not a theorem.

Holomorphy alone would not suffice: determinant nonidentity must be proved separately.

## Post-#142 cell-minimal research correction

The preferred selection remains **DERIVED**:

```text
K* = min { K | exists L in I_Q, AnyParityBad L K }.
```

All smaller sizes are good in both parities throughout the cell, so predecessor size `N*=K*-1` is PSD throughout the cell. #142 preserves the selected bad witness on an open set. Once dense regularity is theorem-backed, choose a regular point inside that open set.

This removes countable all-size Baire regularization and finite-prefix simultaneous regularization from the primary route.

## Smallest remaining obstruction after successful analytic regularity

At the selected regular first-bad state:

```text
A>=0                    from cell/global first-bad minimality
A injective             from regularity
A>0                     finite Hermitian consequence
unique x0 with A x0=b   from #140 regularity scaffold
u0=c-x0.
```

The intended forced countercertificate is

```text
Ecanonical(u0)=Re S0<0.
```

The decisive arithmetic target remains

```text
Ecanonical(c-x0)>=0
```

on the exact forced production state, equivalently `<b,A^-1b><=q_c` once inverse shorthand is justified.

This is substantial new arithmetic. Universal one-step domination remains a valid broad closing condition but is not a reduced subproblem if its proof merely restates successor positivity.

## Current execution order

```text
1. parameter holomorphy of one fixed-unit production core, preferably complexBetaCore
2. reuse for complexAlphaCore and complexGammaCore
3. assemble complex frozen source and intrinsic predecessor remainder holomorphy
4. prove determinant nonidentity
5. derive dense fixed-cell regularity
6. intersect with #142 persistent negativity and package a regular first-bad certificate
7. expose the exact negative regular zero-shift source energy
8. derive an independent arithmetic contradiction from the full pole/arch/scalar/prime source
9. compose to negative-root exclusion
10. explicit Mathlib RiemannHypothesis wrapper
```

## Permanent firewalls

- compiler/CI validity is authoritative; repository presence alone is not;
- theorem authority is through #146 and no further;
- complex/log-cover structure is PROVED; assembled parameter holomorphy is OPEN;
- local scalar analyticity is not full source/predecessor holomorphy;
- translation/deck identity is not holomorphy;
- holomorphy is not determinant nonidentity;
- cell-minimal regularization is DERIVED until merged;
- regularity is not positivity of the successor;
- all-size Baire and finite-prefix regularization are fallback infrastructure, not current dependencies;
- universal determinant positivity cannot count as a reduction if it merely restates successor PSD;
- no `A^-1` at zero before regularity; formal code should prefer the unique-preimage interface;
- `Gamma0*mu(z)=0` with trivial kernel is not a sign theorem;
- D is algebraic, not unitary/isometric;
- no division by unproved transfer/source factors;
- modified-source or generic countermodels are not zeta counterexamples;
- numerical precision is not theorem authority;
- machine claim promotion remains separate;
- RH remains OPEN.

Newest research implications: `research/RHRC/RESEARCH_LEADS_POST_146_APERTURE_ANALYTIC_FRONTIER_DELTA.md`.

**RH remains OPEN.**

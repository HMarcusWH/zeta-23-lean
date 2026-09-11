# RHRC formal audit — theorem authority through PR #148; assembled-holomorphy frontier

> **RH remains OPEN.**

## Current authority split

```text
live main after merged PR #148 = fcd301ae4c1b58196ff7fca18128243f1d35a87b
live main tree = 91d537ee64b8f613bebdcf12110deba486276d35

theorem-state anchor = PR #148 merge fcd301ae4c1b58196ff7fca18128243f1d35a87b
validated theorem head = 77c2d14511004ba380b080e08b4943b267ebd863
validated theorem tree = 91d537ee64b8f613bebdcf12110deba486276d35
RHRC #930 / run 34619665717 = SUCCESS
Permansson #703 / run 34619665725 = SUCCESS

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

These are exact algebraic/production/log-cover theorems. They do not by themselves prove holomorphy.

### PR #145-#146 — scalar removable layer

**PROVED / #145:** the removable scalar factor has value `2` at zero and the repaired scalar factor/remainder is analytic locally at zero.

**PROVED / #146:** for `z!=0`, the removable scalar factor/remainder agrees exactly with the existing production complex scalar/remainder and matches the positive-real production formulas.

### PR #148 — genuine fixed-unit parameter holomorphy

**PROVED:**

```text
complexArchSafeStrip = {z : C | |Im z| < pi}
```

is open, convex, preconnected and connected.

**PROVED:** `complexArchSinhSlope` is zero-free throughout that strip.

**PROVED:** `complexRegularizedArchScale` is differentiable/analytic throughout that strip.

**PROVED:** each exact fixed-unit production core

```text
complexAlphaCore
complexBetaCore
complexGammaCore
```

is differentiable/analytic throughout the strip.

The proof uses genuine differentiation under the fixed `[0,1]` integral with local compact domination. It does not infer holomorphy from the deck law.

## Exact validation evidence for #148

Validated theorem head:

```text
77c2d14511004ba380b080e08b4943b267ebd863
```

Validated theorem tree:

```text
91d537ee64b8f613bebdcf12110deba486276d35
```

Merged main commit:

```text
fcd301ae4c1b58196ff7fca18128243f1d35a87b
```

Merged main has the same theorem tree as the validated PR head.

RHRC run #930 (`34619665717`) succeeded. Permansson run #703 (`34619665725`) also succeeded on the same theorem head.

## What is not yet proved

No theorem currently proves:

```text
production scalar right-half-plane control on the punctured arch strip
common-domain pole denominator zero-freeness / pole holomorphy
holomorphy of complexFrozenCanonicalSourceRemainder
holomorphy of complexFrozenIntrinsicPredecessorRemainder
holomorphy of the lifted predecessor on a connected logarithmic-cover domain
holomorphy/nonidentity of the relevant determinant
dense regular apertures on the physical cutoff cell
production cell-minimal regular first-bad selection
realness of the exact zero-shift coupling in the compression needed for Delta(x0)
regular canonical Schur-energy nonnegativity
negative-root exclusion
outside-strip/trivial-zero terminal seam
RH
```

## Active analytic theorem

The smallest current obstruction is assembled common-domain source/predecessor holomorphy.

The #148 archimedean cores are closed inputs. The remaining production channels are scalar, pole and finite prime/source pieces.

The highest-value scalar lead is

```text
Re(z*coth(z/2))
  = (x*sinh x + y*sin y)/(cosh x - cos y)
```

for `z=x+iy`. On `|y|<pi`, this suggests strict positivity away from zero and therefore a clean principal-log branch on the punctured arch strip.

This is a **LEAD / HYPOTHESIS**, not yet a theorem.

## Translation/deck-law falsification

The exact #144 deck law does not imply holomorphy.

The generic function

```text
F(z)=-z+Re z
```

has affine imaginary-translation behavior of the same structural kind while failing complex differentiability. Therefore any proof that substitutes deck-periodicity or a translation identity for genuine analytic control is invalid.

## Candidate determinant nonidentity argument

Only after assembled lifted holomorphy is established should the #144 deck structure become load-bearing:

```text
Ahat(z+2*pi*i)=Ahat(z)-(2*pi*i)I.
```

If `det Ahat` vanished identically, the intended finite-dimensional argument is to iterate the deck shift at one base point and force the characteristic polynomial of one fixed finite operator to have too many distinct roots.

This remains a **LEAD / HYPOTHESIS**, not a theorem.

The zero-dimensional predecessor case must be split off separately.

## Post-#142 cell-minimal research correction

The preferred selection remains **DERIVED**:

```text
K* = min { K | exists L in I_Q, AnyParityBad L K }.
```

All smaller sizes are good in both parities throughout the cell, so predecessor size `N*=K*-1` is PSD throughout the cell. #142 preserves the selected bad witness on an open set. Once dense regularity is theorem-backed, choose a regular point inside that open set.

The minimum must be taken over the whole cell. A least bad size at one aperture cannot safely be transported to a different aperture.

## Smallest remaining obstruction after successful analytic regularity

At the selected regular first-bad state:

```text
A>=0                    from cell-wide first-bad minimality
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

on the exact forced production state.

A possible smaller certificate is `q_c>=0` plus `Delta(x0)>=0`, but only after Lean proves the zero-shift coupling is real and the `q_A(x0)=0` edge case is handled. Until then this is **DERIVED/LEAD**, not theorem authority.

Universal one-step domination remains a valid broad closing condition but is not a reduced subproblem if its proof merely restates successor positivity.

## Current execution order

```text
1. prove/falsify scalar right-half-plane control on the punctured arch strip
2. close common-domain scalar/pole/prime source holomorphy
3. assemble complex frozen source and intrinsic predecessor remainder holomorphy
4. prove lifted predecessor holomorphy on a connected cover domain
5. prove determinant nonidentity by deck shift + characteristic polynomial
6. derive dense fixed-cell regularity
7. intersect with #142 persistent negativity and package a cell-minimal regular first-bad certificate
8. expose the exact negative regular zero-shift source energy
9. derive an independent arithmetic nonnegative sign from the full pole/arch/scalar/prime source
10. compose to negative-root exclusion
11. close the outside-strip/trivial-zero seam
12. explicit Mathlib RiemannHypothesis wrapper
```

## Permanent firewalls

- compiler/CI validity is authoritative; repository presence alone is not;
- theorem authority is through #148 and no further;
- fixed-unit archimedean parameter holomorphy is PROVED; assembled source/predecessor holomorphy is OPEN;
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
- strip-zero exclusion is not the terminal Mathlib RH theorem without the outside-strip/trivial-zero seam;
- machine claim promotion remains separate;
- RH remains OPEN.

Newest research implications: `research/RHRC/RESEARCH_LEADS_POST_148_PARAMETER_HOLOMORPHY_GREEN_DELTA.md`.

**RH remains OPEN.**

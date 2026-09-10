# Fork notes — current RHRC state

> **RH remains OPEN.**

## Authority snapshot

```text
live main after merged PR #142 = 3e8d2995a1c00a9aef0d8cb0f5382658c91a8673
live main tree = a92d03d0d4ad800d544a835b8ae2e3d23bae2c47

theorem-state anchor = PR #142 merge 3e8d2995a1c00a9aef0d8cb0f5382658c91a8673
validated theorem head = 23d96af9aafd86ad26ae7913c3d6c14503d539de
validated theorem tree = a92d03d0d4ad800d544a835b8ae2e3d23bae2c47
RHRC #889 = SUCCESS
Permansson #662 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

PR #142 is theorem-bearing and advances theorem authority beyond #140. It does not prove determinant nonidentity, dense regular-aperture existence, the final arithmetic Schur sign, negative-root exclusion, or RH.

## Recent theorem packages

```text
#129 source-explicit cubic defect + exact cross-parity secular transfer
#131 exact canonical source-moment decomposition
#134 denominator-free whole-kernel source transport + direct zero-shift transfer
#136 absolute canonical source energy + scalar-sensitive production decomposition
#137 exact source pairing + one-step determinant + global sign-failure endpoint
#140 eventual aperture freedom + predecessor-regularity/frozen-cutoff scaffold
#142 fixed-cell canonical continuity + same-witness local persistence
```

## What #142 adds

**PROVED:** on every physical cutoff cell `I_Q=(log Q,log(Q+1))`, each entry of the actual production `canonicalSourceMatrix` is continuous.

**PROVED:** for any fixed finite coefficient vector, its canonical quadratic energy is continuous on that cell.

**PROVED:** a strict negative witness at one interior aperture persists on an open in-cell neighborhood with the **same finite size and the same vector**.

**PROVED:** combined with #140, an off-line zero supplies such a locally persistent boundary-flat negative witness at every chosen sufficiently large cell-interior aperture.

Headline declarations:

```text
continuousOn_canonicalSourceMatrix_apply_fixedCell
continuousOn_re_canonicalSourceQuadraticForm_fixedCell
exists_open_fixedCell_negativeCanonicalSourceWitness_persistence
eventually_fixedCell_negativeCanonicalSourceWitness_persists_of_offLine_zero
```

## Current frontier after the #142 post-green pass

```text
A4b1 absolute canonical source energy                            PROVED / #136
A4b2a one-step determinant/sufficiency reduction                 PROVED / #137
A4R0  aperture freedom + regularity scaffold                     PROVED / #140
A4R1a fixed-cell canonical witness persistence                   PROVED / #142
A4R1b analytic frozen predecessor + determinant nonidentity      OPEN / NOW
A4R1c cell-minimal regular first-bad selection                   OPEN / NEXT
A4b2r regular minimizing-trial Schur-energy sign                 OPEN / DECISIVE ARITHMETIC GAP
A4b2b universal shell/determinant domination                     OPEN / BROAD FALLBACK
global first-bad exclusion                                       OPEN
terminal Mathlib RH wrapper                                      OPEN
RH                                                               OPEN
```

## Why the regularization problem shrank again

After #140 the preferred plan was to choose one cutoff cell, obtain a finite witness `(N,u)`, preserve it locally, then regularize all predecessor blocks through size `N`.

#142 closes the persistence step. A stronger **DERIVED** selection is now available: choose the least bad size over the entire cutoff cell before choosing the regular aperture.

```text
K* = min { K | exists L in I_Q, AnyParityBad L K }.
```

Then every smaller size is good in both parities throughout the whole cell. At predecessor size `N*=K*-1`, predecessor nonnegativity is therefore uniform across the cell.

Take a negative witness at size `K*`; #142 preserves it on an open `J`. Dense regularity need only intersect that open set for the relevant predecessor determinant(s) at the single size `N*`.

So neither countable all-size Baire regularity nor finite-prefix regularization is a primary dependency.

## Intended A4R1b theorem shape

```text
actual frozen intrinsic predecessor
  -> complex continuation of the production channels
  -> A(L) = -Log(L) I + B(L)
  -> single-valued holomorphic B on a punctured connected domain
  -> logarithmic monodromy / finite-spectrum contradiction if det identically zero
  -> determinant nonidentity
  -> dense regular apertures on every physical cutoff cell.
```

The #140 scalar `-log L` coefficient is already theorem-backed. #142 supplies regularized real archimedean integrands that make direct complexification more concrete.

After the real substitution `x=L t`, the integration interval becomes fixed and the oscillatory frequency no longer moves with aperture. Those rescaled formulas are **DERIVED**, not merged Lean declarations.

## After analytic regularity

At the selected cell-minimal first-bad state:

```text
A>=0                    from cell/global minimality
A injective             from regularity
A>0                     finite Hermitian consequence
unique x0 with A x0=b   #140 scaffold
u0=c-x0.
```

The existing #136/#137 machinery can then be packaged into the forced regular countercertificate

```text
Ecanonical(u0)=Re S0<0.
```

The decisive arithmetic target remains

```text
Ecanonical(c-x0) >= 0
```

or equivalently `<b,A^-1b> <= q_c` once inverse shorthand is legal.

## Falsification state

A new generic analytic centered diagonal family has all of the following simultaneously:

```text
explicit -log L scalar term;
predecessor positivity throughout L>0;
persistent finite negative witnesses at every aperture;
a globally minimal bad size;
common negative behavior in both parities.
```

It is not the canonical zeta source. Its purpose is to prove a design firewall: aperture freedom, persistence, minimality, regularity, parity and scalar logarithms do not by themselves generate the contradiction. The actual canonical pole/archimedean/von-Mangoldt arithmetic must do new work.

See `research/RHRC/countermodels/POST_142_REGULARIZATION_COUNTERMODEL_2026_09_10.md`.

## Firewalls

- RH remains OPEN.
- theorem authority is through #142 only.
- fixed-cell persistence is PROVED; analyticity, determinant nonidentity and dense regularity are OPEN.
- cell-minimal regularization is DERIVED until production-packaged.
- regularity is not successor positivity.
- the regular scalar sign theorem is OPEN.
- no all-size Baire or finite-prefix regularization should be built unless the smaller route fails for a theoremized reason.
- no zero-shift inverse is required in Lean before regularity; use the unique-preimage interface.
- no termwise source-atom positivity shortcut.
- no factorwise division by unproved transfer quantities.
- D remains algebraic, not unitary/isometric.
- machine claim promotion remains separate.

Newest research detail: `research/RHRC/RESEARCH_LEADS_POST_142_FIXED_CELL_PERSISTENCE_DELTA.md`.

**RH remains OPEN.**
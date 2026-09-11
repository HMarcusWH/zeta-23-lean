# Fork notes — current RHRC state

> **RH remains OPEN.**

## Authority snapshot

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

## Recent theorem packages

```text
#129 source-explicit cubic defect + exact cross-parity secular transfer
#131 exact canonical source-moment decomposition
#134 denominator-free whole-kernel source transport + direct zero-shift transfer
#136 absolute canonical source energy + scalar-sensitive production decomposition
#137 exact source pairing + one-step determinant + global sign-failure endpoint
#140 eventual aperture freedom + predecessor-regularity/frozen-cutoff scaffold
#142 fixed-cell canonical continuity + same-witness local persistence
#144 exact frozen production source/predecessor + logarithmic-cover scaffold
#145 local removable scalar analyticity at zero
#146 removable scalar/remainder <-> production complex scalar/remainder
```

## What #144 adds

**PROVED:** exact frozen canonical source equality with the actual production source on a physical cutoff cell.

**PROVED:** exact `-log(L) * I + remainder` decomposition survives the actual parity compression and intrinsic predecessor projection.

**PROVED:** exact complex frozen source/predecessor remainder and positive-real bridges.

**PROVED:** logarithmic-cover lift

```text
Ahat(z) = -z I + R(exp z)
```

with exact deck-periodicity of the lifted remainder and exact affine deck shift for the full lifted block.

**PROVED:** evaluating the lifted family at `z=log L` on a physical cutoff cell recovers the production `intrinsicPredecessorBlock`.

## What #145-#146 add

**PROVED / #145:** the corrected scalar aperture factor and scalar remainder have a removable analytic extension at zero.

**PROVED / #146:** away from zero, that removable scalar layer is exactly the existing production complex scalar/remainder; on `L>0`, it is exactly the production real scalar formula.

This closes the scalar removable-point/provenance issue without modifying the production definitions.

## Current frontier

```text
A4b1 absolute canonical source energy                            PROVED / #136
A4b2a one-step determinant/sufficiency reduction                 PROVED / #137
A4R0  aperture freedom + regularity scaffold                     PROVED / #140
A4R1a fixed-cell canonical witness persistence                   PROVED / #142
A4R1b frozen/log-cover predecessor scaffold                      PROVED / #144
A4R1b scalar removable analyticity + production bridge           PROVED / #145-#146
A4R1b parameter-integral + assembled holomorphy                  OPEN / NOW
A4R1b determinant nonidentity + dense regularity                 OPEN / NEXT
A4R1c cell-minimal regular first-bad selection                   OPEN / NEXT
A4b2r regular minimizing-trial Schur-energy sign                 OPEN / DECISIVE ARITHMETIC GAP
A4b2b universal shell/determinant domination                     OPEN / BROAD FALLBACK
global first-bad exclusion                                       OPEN
terminal Mathlib RH wrapper                                      OPEN
RH                                                               OPEN
```

## The remaining analytic gap is narrower

The complex/log-cover family now exists. The next theorem is not another algebraic continuation identity. It is genuine complex differentiability of the fixed-unit parameter integrals that feed the exact complex source.

The preferred prototype is `complexBetaCore`:

```text
fixed domain [0,1]
+ pointwise complex differentiability in z
+ local denominator nonvanishing/control
+ locally uniform integrable domination
-> differentiation under the integral
-> Analytic / Holomorphic in z.
```

After that, reuse the proof pattern for `complexAlphaCore` and `complexGammaCore`, then assemble source/predecessor holomorphy.

## Translation/deck-law firewall

The exact deck law from #144 is structural, not analytic. The generic function

```text
F(z)=-z+Re z
```

has the same kind of affine imaginary-translation behavior while being nonholomorphic. This permanently blocks any shortcut from deck/translation identity to holomorphy.

## Cell-minimal compression

The post-#142 **DERIVED** selection remains preferred:

```text
K* = min { K | exists L in I_Q, AnyParityBad L K }.
```

Then all smaller sizes are good in both parities throughout the cell; predecessor size `K*-1` is PSD across the cell; #142 preserves one selected bad witness on an open set; and eventual dense regularity only has to meet that open set at the single predecessor size.

## After analytic regularity

At the selected cell-minimal regular first-bad state:

```text
A>=0
A injective
A>0
unique x0 with A x0=b
u0=c-x0.
```

The existing #136/#137 machinery can then be packaged into the forced regular negative countercertificate

```text
Ecanonical(u0)=Re S0<0.
```

The decisive arithmetic target remains

```text
Ecanonical(c-x0)>=0
```

or equivalently `<b,A^-1b> <= q_c` after regularity.

## Falsification state

Two negative controls are active:

1. the post-#142 generic analytic regularization countermodel shows that persistence + minimality + regularity + parity + scalar logarithm do not force the contradiction;
2. the post-#146 `-z+Re z` countermodel shows that translation/deck structure does not imply holomorphy.

Neither is a counterexample to the actual canonical source or to RH.

## Firewalls

- RH remains OPEN.
- theorem authority is through #146 only.
- exact frozen/log-cover continuation is PROVED; assembled parameter holomorphy is OPEN.
- local scalar analyticity is not full source/predecessor analyticity.
- deck-periodicity is not holomorphy.
- holomorphy is not determinant nonidentity.
- cell-minimal regularization is DERIVED until production-packaged.
- regularity is not successor positivity.
- the regular scalar/Schur sign theorem is OPEN.
- no all-size Baire or finite-prefix regularization should be built unless the smaller route fails for a theoremized reason.
- no zero-shift inverse is required in Lean before regularity; use the unique-preimage interface.
- no termwise source-atom positivity shortcut.
- no factorwise division by unproved transfer quantities.
- D remains algebraic, not unitary/isometric.
- machine claim promotion remains separate.

Newest research detail: `research/RHRC/RESEARCH_LEADS_POST_146_APERTURE_ANALYTIC_FRONTIER_DELTA.md`.

**RH remains OPEN.**

# Fork notes — current RHRC state

> **RH remains OPEN.**

## Authority snapshot

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
#148 connected arch strip + fixed-unit alpha/beta/gamma parameter holomorphy
```

## What #148 adds

**PROVED:** `complexArchSafeStrip = {z : ℂ | |z.im| < pi}` is open, convex and connected.

**PROVED:** `complexArchSinhSlope` is zero-free throughout that strip.

**PROVED:** `complexRegularizedArchScale` is analytic throughout that strip.

**PROVED:** `complexAlphaCore`, `complexBetaCore` and `complexGammaCore` are genuinely analytic in the aperture parameter throughout the strip, via differentiation under the fixed `[0,1]` integral with local compact domination.

**PROVED:** real-axis analyticity corollaries for those cores do not require positivity of the real parameter.

This closes the old fixed-unit parameter-integral first break without changing Eq. (4.4) normalization or using the deck law as a substitute for holomorphy.

## Current frontier

```text
A4b1 absolute canonical source energy                            PROVED / #136
A4b2a one-step determinant/sufficiency reduction                 PROVED / #137
A4R0  aperture freedom + regularity scaffold                     PROVED / #140
A4R1a fixed-cell canonical witness persistence                   PROVED / #142
A4R1b frozen/log-cover predecessor scaffold                      PROVED / #144
A4R1b scalar removable analyticity + production bridge           PROVED / #145-#146
A4R1b alpha/beta/gamma parameter holomorphy                      PROVED / #148
A4R1b assembled source/predecessor holomorphy                    OPEN / NOW
A4R1b determinant nonidentity + dense regularity                 OPEN / NEXT
A4R1c cell-minimal regular first-bad selection                   OPEN / NEXT
A4b2r regular minimizing-trial Schur-energy sign                 OPEN / DECISIVE ARITHMETIC GAP
A4b2b universal shell/determinant domination                     OPEN / BROAD FALLBACK
global first-bad exclusion                                       OPEN
outside-strip/trivial-zero + terminal Mathlib RH wrapper          OPEN
RH                                                               OPEN
```

## The remaining analytic gap

The production source still contains non-arch channels. The next proof must put all of these on one common complex domain:

```text
production scalar/principal-log branch
pole denominator / pole matrix
finite prime/source terms
#148 arch cores
```

and then assemble

```text
complexFrozenCanonicalSourceRemainder
complexFrozenIntrinsicPredecessorRemainder
liftedFrozenIntrinsicPredecessorBlock
```

as analytic families.

The natural candidate base domain is the punctured arch strip. A high-value lead is the expected strict positivity

```text
Re(z*coth(z/2)) > 0
```

for `|Im z|<pi`, `z!=0`, which would give a clean right-half-plane principal-log branch for the production scalar factor.

## Translation/deck-law firewall

The exact deck law from #144 is structural, not analytic. The generic function

```text
F(z)=-z+Re z
```

has the same kind of affine imaginary-translation behavior while being nonholomorphic. This permanently blocks any shortcut from deck/translation identity to holomorphy.

## Determinant nonidentity lead

Once the lifted predecessor is analytic on a connected domain, the exact law

```text
Ahat(z+2*pi*i)=Ahat(z)-(2*pi*i)I
```

suggests a finite characteristic-polynomial root-count proof that the determinant is not identically zero. This is still a **LEAD / HYPOTHESIS**.

The zero-dimensional predecessor case must be handled directly rather than forced through a positive-degree root-count argument.

## Cell-minimal compression

The post-#142 **DERIVED** selection remains preferred:

```text
K* = min { K | exists L in I_Q, AnyParityBad L K }.
```

Then all smaller sizes are good in both parities throughout the cell; predecessor size `K*-1` is PSD across the cell; #142 preserves one selected bad witness on an open set; and dense regularity only has to meet that open set at the single predecessor size.

The minimum must be taken over the whole cell. Choosing a least bad size at one aperture and then moving the aperture is not enough.

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
Ecanonical(c-x0)>=0.
```

A narrower possible certificate is `q_c>=0` plus `Delta(x0)>=0`, but only after theoremizing zero-shift coupling realness and the zero-energy edge case.

## Firewalls

- RH remains OPEN.
- theorem authority is through #148 only.
- fixed-unit alpha/beta/gamma parameter holomorphy is PROVED.
- assembled source/predecessor holomorphy is OPEN.
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
- strip-zero exclusion is not yet the full Mathlib RH statement without outside-strip/trivial-zero bookkeeping.
- machine claim promotion remains separate.

Newest research detail: `research/RHRC/RESEARCH_LEADS_POST_148_PARAMETER_HOLOMORPHY_GREEN_DELTA.md`.

**RH remains OPEN.**

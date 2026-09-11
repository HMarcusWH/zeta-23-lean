# R003 — CCM / finite Weil bridge

Status: **ACTIVE. THEOREM AUTHORITY THROUGH PR #148. CURRENT FRONTIER = ASSEMBLED SOURCE/PREDECESSOR HOLOMORPHY ON A COMMON DOMAIN, THEN DETERMINANT NONIDENTITY / DENSE FIXED-CELL REGULARITY, THEN REGULAR CANONICAL SCHUR-ENERGY SIGN. RH OPEN.**

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

## Closed internal ladder

```text
F1 finite canonical obstruction                                  PROVED / #94
constrained / Euclidean finite wall                              PROVED / #96-#98
N-FLOW fixed-L negative tail                                     PROVED / #100
PARITY reversal / D-equivalence                                  PROVED / #102-#103
global first bad + nonnegative predecessors                      PROVED / #105,#112
negative mode + KKT + cubic channel                              PROVED / #107,#109,#110
V=W⊕S + shifted/zero-shift Schur package                         PROVED / #113-#128
source-explicit parity transfer                                  PROVED / #129
exact source-moment decomposition                                PROVED / #131
whole-kernel zero-shift source transport                         PROVED / #134
absolute canonical source energy                                 PROVED / #136
exact canonical source pairing                                   PROVED / #137
one-step determinant/channel formula                             PROVED / #137
off-line zero -> q_c<0 OR exists Delta<0                        PROVED / #137
eventual negative witness at every sufficiently large aperture   PROVED / #140
eventual AnyParityBad + fresh global-first-bad selection         PROVED / #140
actual predecessor det!=0 <-> injective + unique preimage        PROVED / #140
frozen prime-cell equality + threshold zero + scalar -log split  PROVED / #140
actual canonical source continuity on a physical cutoff cell     PROVED / #142
same-size/same-vector strict negative witness persistence        PROVED / #142
exact frozen production source/predecessor scaffold              PROVED / #144
exact -log(L) identity split through intrinsic projection        PROVED / #144
complex frozen remainder + log-cover/deck identities             PROVED / #144
local removable scalar analyticity at zero                       PROVED / #145
removable scalar/remainder <-> production complex scalar         PROVED / #146
connected arch strip + regularized arch scale holomorphy         PROVED / #148
complexAlphaCore parameter holomorphy                            PROVED / #148
complexBetaCore parameter holomorphy                             PROVED / #148
complexGammaCore parameter holomorphy                            PROVED / #148
```

## Exact #136/#137 block objects

For the canonical one-step block:

```text
A = intrinsic predecessor block
c = intrinsic cubic shell
b = P_W T c
q_A(w) = Re<Aw,w>
q_c = Re<Tc,c>
Delta(w) = q_c*q_A(w) - |<w,b>|^2.
```

#136 provides scalar-sensitive self-energy and exact pole/arch/scalar/prime channel decomposition. #137 extends that bookkeeping to the exact complex pairing and determinant.

`canonicalOneStepDomination` is exactly

```text
q_c >= 0
AND
forall w, Delta(w) >= 0.
```

It is a proposition/certificate, not a proved property of the canonical source.

## A4R0 / A4R1a — closed before the analytic lift

**PROVED / #140:** a hypothetical off-line zero forces a finite negative canonical witness at every sufficiently large aperture, and the actual predecessor determinant/injectivity, unique-preimage, frozen-cutoff and scalar-log interfaces are theorem-locked.

**PROVED / #142:** on one physical cutoff cell `I_Q=(log Q,log(Q+1))` with `Q>=1`, the actual production `canonicalSourceMatrix` is entrywise continuous and every fixed-vector real quadratic energy is continuous. A strict negative witness at one interior aperture therefore persists on an open `J subset I_Q` with the same finite size and the same vector.

## A4R1b after #144-#148 — exact state

### PROVED / #144

The exact frozen production source and intrinsic predecessor are theorem-locked, including:

```text
frozenCanonicalSourceMatrix_eq_canonicalSourceMatrix_fixedCell
frozenCanonicalSourceMatrix_eq_neg_log_identity_add_remainder
frozenIntrinsicPredecessorBlock_eq_actual_fixedCell
frozenIntrinsicPredecessorBlock_eq_neg_log_id_add_remainder
intrinsicPredecessorBlock_eq_neg_log_id_add_remainder_fixedCell
complexFrozenIntrinsicPredecessorRemainder_ofReal
liftedFrozenIntrinsicPredecessorRemainder_add_two_pi_I
liftedFrozenIntrinsicPredecessorBlock_add_two_pi_I
liftedFrozenIntrinsicPredecessorBlock_of_log_fixedCell
```

Thus the route has an exact lifted object

```text
Ahat(z) = -z I + R(exp z)
```

with exact deck-periodicity of `R(exp z)` and exact recovery of the real production predecessor on a physical cell.

### PROVED / #145-#146

The scalar aperture factor/remainder admits the theoremized removable analytic extension at zero and agrees exactly with the production complex scalar/remainder on `z != 0`, with positive-real production provenance.

### PROVED / #148

The exact fixed-unit archimedean source cores are now genuinely analytic in the complex aperture parameter on the connected strip

```text
complexArchSafeStrip = { z : C | |Im z| < pi }.
```

In particular:

```text
complexArchSinhSlope_ne_zero_of_mem_strip
analyticOnNhd_complexRegularizedArchScale_strip
analyticOnNhd_complexAlphaCore_strip
analyticOnNhd_complexBetaCore_strip
analyticOnNhd_complexGammaCore_strip
```

are compiler-validated.

### OPEN / PRIMARY REDUCTION TARGET

The full production source is not yet theoremized as holomorphic on one common domain. The remaining channels are:

```text
production scalar/principal-log branch
pole denominator / pole matrix
finite prime/source channel
fixed finite source assembly
intrinsic projection
logarithmic-cover lift.
```

The next first break is therefore:

```text
common punctured source domain
  -> scalar branch control
  -> pole zero-free control
  -> finite source analyticity
  -> complexFrozenCanonicalSourceRemainder holomorphy
  -> complexFrozenIntrinsicPredecessorRemainder holomorphy
  -> lifted predecessor holomorphy on a connected cover domain.
```

## Scalar right-half-plane lead

A high-value common-domain lead is

```text
z*(exp z + 1)/(exp z - 1) = z*coth(z/2)
```

with expected real-part formula

```text
Re(z*coth(z/2))
  = (x*sinh x + y*sin y)/(cosh x - cos y),  z=x+iy.
```

For `|y|<pi`, the numerator terms are nonnegative and the denominator is positive away from zero. If Lean closes the strict positivity theorem, the production scalar factor stays in the right half-plane on the punctured arch strip, giving a natural principal-log branch on the same domain.

**Status: LEAD / HYPOTHESIS.**

## Translation/deck-law firewall

The exact deck law from #144 is useful structure, not an analyticity theorem.

The generic negative control

```text
F(z) = -z + Re z
```

has the same kind of affine imaginary-translation law while failing complex differentiability. Therefore any argument of the form

```text
translation/deck identity
-> holomorphy
```

is invalid without a genuine analytic proof.

## Determinant nonidentity mechanism — after assembled holomorphy

Once holomorphy of the actual lifted predecessor is theorem-backed, use

```text
Ahat(z+2*pi*i)=Ahat(z)-(2*pi*i)I.
```

Iterating at one base point gives finitely many distinct scalar shifts of one fixed finite operator. If `det Ahat` vanished identically, its characteristic polynomial would have too many roots. This is the intended algebraic nonidentity proof.

The zero-dimensional predecessor case must be split off directly; do not force a positive-degree root-count argument through `finrank=0`.

Holomorphy and determinant nonidentity remain separate proof obligations.

## Post-#142 route compression — cell-minimal size first

**DERIVED / PRIMARY DESIGN.**

Minimize bad size over the whole cutoff cell:

```text
K* = min { K | exists L in I_Q, AnyParityBad L K }.
```

Then every `K<K*` is good in both parities throughout the cell, so predecessor size `N*=K*-1` is PSD throughout the cell. Choose a bad parity witness at `(L*,K*)`; #142 preserves the same witness on an open `J subset I_Q`. If the relevant predecessor determinant is nonzero on a dense subset, choose a regular aperture in `J`.

This cell-wide minimization is essential. A least bad size chosen only at one aperture is not stable after moving the aperture.

For the bad parity's negative Schur-energy reduction, only that parity's predecessor needs regularizing. Regularizing both parities remains a useful stronger option.

The production cell-minimal composition is not yet a merged theorem.

## Next route — regular canonical Schur-energy sign

If analytic regularity succeeds, compose dense regularity with the cell-minimal bad state and #142 persistent-negative open set.

At the selected state:

```text
A>=0                    from cell-wide minimality
A injective             from regularity
A>0                     finite Hermitian consequence
unique x0 with A x0=b   #140 scaffold
u0=c-x0.
```

Use the unique-preimage interface in Lean rather than making inverse notation load-bearing.

The intended packaged forced countercertificate is

```text
Ecanonical(u0) = Re S0 < 0.
```

The decisive arithmetic target becomes

```text
Ecanonical(c-x0) >= 0.
```

A possible narrower reduction is to prove the zero-shift coupling is real and then use `q_c>=0` together with `Delta(x0)>=0`. This remains **DERIVED/LEAD** until the exact coupling-realness and zero-energy edge case are theoremized.

## Stronger falsification constraints

Two independent negative controls remain active:

1. `POST_142_REGULARIZATION_COUNTERMODEL_2026_09_10.md`: persistence + minimality + regularity + parity + scalar logarithm do not force a contradiction in a generic analytic family.
2. `POST_146_TRANSLATION_NOT_HOLOMORPHY_COUNTERMODEL_2026_09_11.md`: translation/deck structure does not imply holomorphy.

Neither is a counterexample to the actual canonical source or to RH.

## Universal domination fallback

Universal `q_c>=0` and `Delta(w)>=0` for every predecessor direction remains a valid closing theorem. It is deferred rather than killed. Promote it again only if a genuinely independent positive canonical source representation or exact arithmetic remainder is found.

## Permanent normalization / claim firewalls

- canonical sign-sensitive object is `canonicalSourceMatrix` under the repaired source convention;
- legacy `finiteMatrix` cannot supply absolute sign automatically;
- theorem authority is through #148;
- aperture freedom and same-witness persistence are PROVED;
- exact frozen/log-cover construction and scalar production bridge are PROVED;
- fixed-unit alpha/beta/gamma parameter holomorphy is PROVED;
- genuine assembled source/predecessor holomorphy is OPEN;
- translation/deck identities are not holomorphy;
- determinant nonidentity / dense regularity are OPEN;
- cell-minimal regular selection is DERIVED until production-packaged;
- regular canonical Schur-energy nonnegativity is OPEN;
- regularity alone does not exclude a negative successor;
- no all-size Baire or finite-prefix regularization is required unless the smaller cell-minimal route fails for a theoremized reason;
- no inverse is load-bearing before regularity; prefer unique preimage;
- no division by unproved transfer factors;
- D is algebraic, not unitary/isometric;
- generic/modified-source countermodels do not refute canonical CCM;
- numerical precision is not theorem authority;
- terminal strip-zero exclusion still needs an explicit outside-strip/trivial-zero bridge to Mathlib `RiemannHypothesis`;
- RH remains OPEN.

Detailed current implications: `../../RESEARCH_LEADS_POST_148_PARAMETER_HOLOMORPHY_GREEN_DELTA.md`.

**RH remains OPEN.**

# R003 — CCM / finite Weil bridge

Status: **ACTIVE. THEOREM AUTHORITY THROUGH PR #146. CURRENT FRONTIER = GENUINE APERTURE-PARAMETER HOLOMORPHY OF THE FIXED-UNIT PRODUCTION SOURCE INTEGRALS, THEN DETERMINANT NONIDENTITY / DENSE FIXED-CELL REGULARITY, THEN REGULAR CANONICAL SCHUR-ENERGY SIGN. RH OPEN.**

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

## A4R1b after #144-#146 — exact state

The old first break "construct the actual frozen complex predecessor and isolate the scalar logarithm" is now closed.

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

### PROVED / #145

The scalar aperture factor/remainder admits the theoremized removable analytic extension at zero.

### PROVED / #146

The removable scalar factor/remainder agrees exactly with the production complex scalar/remainder on `z != 0` and with the positive-real production formulas.

### OPEN / PRIMARY REDUCTION TARGET

No theorem yet proves that the non-scalar parameter-dependent fixed-unit source integrals are holomorphic in the aperture parameter. Consequently no theorem yet proves `complexFrozenIntrinsicPredecessorRemainder` is holomorphic.

The first break is therefore:

```text
fixed-unit production source integral
  -> local zero-free / denominator control
  -> pointwise complex parameter derivative
  -> locally uniform integrable domination
  -> differentiation under the integral
  -> holomorphy of complexBetaCore / complexAlphaCore / complexGammaCore
  -> assembled frozen source holomorphy
  -> assembled intrinsic predecessor remainder holomorphy.
```

Prototype the simplest core first, preferably `complexBetaCore`.

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

See `../../countermodels/POST_146_TRANSLATION_NOT_HOLOMORPHY_COUNTERMODEL_2026_09_11.md`.

## Determinant nonidentity mechanism — after holomorphy only

Once holomorphy of the actual lifted predecessor is theorem-backed, the exact #144 structure becomes load-bearing:

```text
Ahat(z) = -z I + R(exp z)
R(exp(z+2*pi*i)) = R(exp z).
```

If `det Ahat` vanished identically, the same finite-dimensional operator `R(exp z0)` would be forced to support too many distinct scalar shifts/eigenvalues as `z0` is translated by `2*pi*i*k`.

This is a **LEAD / HYPOTHESIS** until the determinant nonidentity theorem is formally proved. Holomorphy alone is not enough; `det Ahat` could in principle still be identically zero.

## Post-#142 route compression — cell-minimal size first

**DERIVED / PRIMARY DESIGN.**

Minimize bad size over the whole cutoff cell:

```text
K* = min { K | exists L in I_Q, AnyParityBad L K }.
```

Then every `K<K*` is good in both parities throughout the cell, so predecessor size `N*=K*-1` is PSD throughout the cell. Choose a bad parity witness at `(L*,K*)`; #142 preserves the same witness on an open `J subset I_Q`. If the relevant predecessor determinant is nonzero on a dense subset, choose a regular aperture in `J`.

For the bad parity's negative Schur-energy reduction, only that parity's predecessor needs regularizing. Regularizing both parities remains a useful stronger option.

The production cell-minimal composition is not yet a merged theorem.

## Next route — regular canonical Schur-energy sign

If analytic regularity succeeds, compose dense regularity with the cell-minimal bad state and #142 persistent-negative open set.

At the selected state:

```text
A>=0                    from cell/global minimality
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
Ecanonical(c-x0) >= 0
```

on that exact forced regular trial, equivalently in inverse shorthand

```text
<b,A^-1b> <= q_c.
```

This theorem must use exact canonical pole/arch/scalar/prime interaction. An auxiliary positive form whose positivity is equivalent to successor PSD is circular.

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
- theorem authority is through #146;
- aperture freedom and same-witness persistence are PROVED;
- exact frozen/log-cover construction and scalar production bridge are PROVED;
- genuine assembled parameter holomorphy is OPEN;
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
- RH remains OPEN.

Detailed current implications: `../../RESEARCH_LEADS_POST_146_APERTURE_ANALYTIC_FRONTIER_DELTA.md`.

**RH remains OPEN.**

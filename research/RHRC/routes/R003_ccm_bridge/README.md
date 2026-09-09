# R003 — CCM / finite Weil bridge

Status: **ACTIVE. THEOREM AUTHORITY THROUGH PR #140. CURRENT FRONTIER = FIXED-CELL FINITE REGULAR-APERTURE SELECTION, THEN REGULAR CANONICAL SCHUR-ENERGY SIGN. RH OPEN.**

## Current authority split

```text
live main after merged PR #140 = fa96196b5bd6ed754853b0bdacee1dbd2356022f
live main tree = 2015404927540ae79a64469af82813463694b71d

theorem-state anchor = PR #140 merge fa96196b5bd6ed754853b0bdacee1dbd2356022f
validated theorem head = 77b52cfc73dfd83d2a0ed4373befba97d77e48e5
validated theorem tree = 2015404927540ae79a64469af82813463694b71d
RHRC #882 = SUCCESS
Permansson #655 = SUCCESS

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
domination -> zero-shift preimage + endpoint >=0                 PROVED / #137 CONDITIONAL
domination -> no safe negative explicit Schur root               PROVED / #137 CONDITIONAL
off-line zero -> q_c<0 OR exists Delta<0                        PROVED / #137
eventual negative witness at every sufficiently large aperture   PROVED / #140
eventual AnyParityBad + fresh global-first-bad selection         PROVED / #140
actual predecessor det!=0 <-> injective + unique preimage        PROVED / #140
frozen prime-cell equality + threshold zero + scalar -log split  PROVED / #140
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

## Post-#140 route correction

The post-#138 circularity result still stands:

```text
A>=0 and one-dimensional shell:
canonicalOneStepDomination
  <-> successor one-step quadratic form is nonnegative.
```

#140 then changes the aperture-selection quantifiers:

```text
off-line zero
  -> finite negative canonical witness at every sufficiently large aperture.
```

Therefore the active route should choose a convenient frozen cutoff cell **before** choosing the final finite witness.

## A4R0 — aperture freedom and regularity scaffold

**PROVED / #140.**

The new theorem modules supply:

```text
ApertureFreedom.lean
  every sufficiently large aperture has a finite negative witness
  every sufficiently large aperture has AnyParityBad
  every sufficiently large aperture admits a fresh least global-first-bad

CanonicalApertureRegularityScaffold.lean
  predecessor determinant nonzero <-> injective
  regular predecessor -> unique target preimage
  regular predecessor -> unique cubic zero-shift preimage
  frozen prime matrix equality on floor(exp L)=Q cells
  threshold source atom equals zero at L=log q
  exact real-axis -log(L) scalar extraction.
```

These are interfaces, not the dense regularity theorem.

## Current route — A4R1 fixed-cell finite regularization

**OPEN / PRIMARY REDUCTION TARGET.**

Choose a large integer `Q` and work strictly inside

```text
log Q < L < log(Q+1).
```

The cutoff is constant throughout this cell. Then:

```text
choose interior L1
-> #140 gives finite N,u with Ecanonical(L1,N,u)<0
-> prove continuity for this fixed N,u
-> obtain a neighborhood J where the same u remains negative
-> prove each fixed intrinsic predecessor determinant has dense nonzero set
-> intersect only both parities and 1<=k<=N
-> choose L2 in J with those finitely many regular predecessors
-> preserve the same negative witness
-> freshly reselect global first-bad at L2.
```

Because the preserved negative witness is still bad at size `N`, the reselected first-bad size is at most `N`; the finite regularity horizon therefore covers the reselected state.

### What this removes from the primary route

- no countable all-size Baire theorem;
- no threshold crossing during the regularizing move;
- no assumption that the old least-bad index persists.

Countable/Baire regularization is retained only as fallback if the finite-cell route fails for a theoremized reason.

## Fixed-block analytic target

For each fixed `Q,p,N`, work on the determinant of the actual projected predecessor block.

The desired theorem chain is:

```text
full frozen production predecessor admits suitable complex/log-cover continuation
-> Ahat(z)=-z I+Rhat(z)
-> Rhat(z+2*pi*i)=Rhat(z)
-> determinant is not identically zero
-> regular real apertures are dense in the cutoff cell.
```

The #140 theorem already validates the scalar real-axis `-log(L)` contribution in `wCorrection`. The unresolved step is the full projected-block remainder.

The archimedean channel is the main analytic hazard. Before building new raw integral analyticity, inspect and reuse:

```text
DictionaryArchPhysical.lean
DictionaryArchBridge.lean
GammaFacts/Mu.lean
```

The old dictionary/digamma bridge is a **RESURRECTED LEAD** because #140 makes aperture analyticity newly central.

The invalid shortcut that treats physical `A(exp z)` as simultaneously periodic and equal to `-zI+periodic` without a genuine log-cover continuation remains forbidden.

## Next route — regular canonical Schur-energy sign

If A4R1 succeeds, the reselected first-bad state has predecessor nonnegativity from minimality and injectivity from regularization. #140 then supplies a unique `x0` with

```text
A x0 = b.
```

Use this unique-preimage interface in Lean rather than making inverse notation load-bearing.

Set

```text
u0 = c - x0.
```

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

This theorem must use exact canonical prime/arch/scalar interaction. An auxiliary positive form whose positivity is equivalent to successor PSD is circular.

## Preserved derived geometry and diagnostics

The post-#138 audit records, not as new Lean authority:

```text
k = P_(ker A)b
Delta(k) = -||k||^4
```

and an explicit determinant formula for the root-selected predecessor vector at a safe negative root.

It also reports

```text
d = -(6/(2*N-1)) a
```

for the two #134 correction vectors, supported by exact rational checks.

Discovery constraints remain:

- negative leading source-atom determinant coefficient: do not default to atomwise positive determinant/SOS;
- extreme sampled canonical Schur cancellation: independent channel majorants require exceptional justification;
- modified prime-weight sensitivity: exact arithmetic coefficients matter sharply;
- all such findings are DERIVED/external or EXPERIMENTAL, not theorem authority.

The preferred discovery observable after A4R1 is the **full minimizing-trial Schur remainder** on `u0`, simplified using `A x0=b` before inequalities are attempted.

## Universal domination fallback

Universal `q_c>=0` and `Delta(w)>=0` for every predecessor direction remains a valid closing theorem. It is deferred rather than killed. Promote it again if a genuinely independent positive canonical source representation or exact arithmetic remainder is found.

## Permanent normalization / claim firewalls

- canonical sign-sensitive object is `canonicalSourceMatrix` under the repaired source convention;
- legacy `finiteMatrix` cannot supply absolute sign automatically;
- theorem authority is through #140;
- aperture freedom is PROVED;
- dense fixed-cell regular-aperture selection is OPEN;
- regular canonical Schur-energy nonnegativity is OPEN;
- regularity alone does not exclude a negative successor;
- no all-size Baire theorem is required unless finite-cell selection fails for a theoremized reason;
- no inverse is load-bearing before regularity; prefer unique preimage;
- no division by unproved transfer factors;
- D is algebraic, not unitary/isometric;
- generic/modified-source countermodels do not refute canonical CCM;
- numerical precision is not theorem authority;
- RH remains OPEN.

Detailed current implications: `../../RESEARCH_LEADS_POST_140_APERTURE_FREEDOM_DELTA.md`.

**RH remains OPEN.**
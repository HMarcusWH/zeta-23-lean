# R003 — CCM / finite Weil bridge

Status: **ACTIVE. THEOREM AUTHORITY THROUGH PR #137. POST-#138 RESEARCH FRONTIER = REGULAR-APERTURE SELECTION, THEN REGULAR CANONICAL SCHUR-ENERGY SIGN. RH OPEN.**

## Current authority split

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
```

## Exact #136/#137 objects

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

## Post-#138 route correction

The independent Astra audit sharpens the post-#137 circularity warning:

```text
A>=0 and one-dimensional shell:
canonicalOneStepDomination
  <-> successor one-step quadratic form is nonnegative.
```

Universal A4b2b therefore remains a correct sufficient closing theorem but is not presently a smaller subproblem.

The R003 active route now attempts to remove only singular predecessor geometry before spending arithmetic effort on the final regular scalar.

## Current route — A4R regular-aperture selection

**OPEN / PRIMARY REDUCTION TARGET.**

Prove that a strict finite canonical negative witness can be moved to an arbitrarily nearby positive aperture such that:

- the same witness remains negative before reselection;
- every finitely relevant predecessor block in both parities is injective/positive definite;
- the global first-bad index is selected again at the new aperture.

Candidate mechanism:

```text
freeze prime cutoff Q
M_Q(L) = -log(L) I + B_Q(L)
L = exp(z)
periodic Bhat_Q(z)
characteristic-polynomial root count
-> determinant nonidentity
-> dense regular apertures.
```

Acceptance requires the exact production source, not a toy family. In particular prove frozen-cutoff analyticity, threshold continuity, fixed-basis/Gram correctness, simultaneous finite avoidance and the exact predecessor-compression bridge.

## Next route — regular canonical Schur-energy sign

If A4R succeeds, both predecessor blocks are positive definite and the forced first-bad state has

```text
x0 = A^-1 b
u0 = c - A^-1 b
S0 = q_c - <b,A^-1 b>
Ecanonical(u0) = Re S0 < 0.
```

The decisive arithmetic target becomes

```text
Ecanonical(c - A^-1 b) >= 0
```

on that exact forced regular trial, equivalently

```text
<b,A^-1b> <= q_c.
```

This theorem must use exact canonical prime/arch/scalar interaction. An auxiliary positive form whose positivity is equivalent to successor PSD is circular.

## Preserved derived geometry

The post-#138 audit records, not yet as new Lean authority:

```text
k = P_(ker A)b
Delta(k) = -||k||^4
```

and an explicit determinant formula for `w_lambda=(A-lambda I)^-1b` at the safe negative root.

It also reports

```text
d = -(6/(2*N-1)) a
```

for the two #134 correction vectors, supported by exact rational checks. This should prevent investment in false independence arguments.

## Discovery/falsification constraints

- reported negative leading source-atom determinant coefficient: do not default to atomwise positive determinant/SOS;
- reported canonical Schur cancellation ratios around `6.46e20` in a small sample: coarse independent channel majorants require exceptional justification;
- reported `1e-8` modified prime-weight sensitivity: exact arithmetic coefficients matter sharply;
- all such findings are DERIVED/external or EXPERIMENTAL, not theorem authority.

The preferred discovery observable after A4R is the **full minimizing-trial Schur remainder** on `u0`, including exact mixed channel cancellation and prime-weight sensitivities.

## Universal domination fallback

Universal `q_c>=0` and `Delta(w)>=0` for every predecessor direction remains a valid closing theorem. It is deferred rather than killed. Promote it again if a genuinely independent positive canonical source representation or exact arithmetic remainder is found.

## Permanent normalization / claim firewalls

- canonical sign-sensitive object is `canonicalSourceMatrix` under the repaired source convention;
- legacy `finiteMatrix` cannot supply absolute sign automatically;
- theorem authority remains #137;
- regular-aperture selection is OPEN;
- regular canonical Schur-energy nonnegativity is OPEN;
- regularity alone does not exclude a negative successor;
- no `A^-1` at zero before regularity;
- no division by unproved transfer factors;
- D is algebraic, not unitary/isometric;
- generic/modified-source countermodels do not refute canonical CCM;
- numerical precision is not theorem authority;
- RH remains OPEN.

Detailed current implications: `../../RESEARCH_LEADS_POST_138_ASTRA_DELTA.md`.

**RH remains OPEN.**
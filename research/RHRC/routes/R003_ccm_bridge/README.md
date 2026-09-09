# R003 — CCM / finite Weil bridge

Status: **ACTIVE. THEOREM AUTHORITY THROUGH PR #137. ABSOLUTE SOURCE ENERGY, EXACT SOURCE PAIRING, ONE-STEP DETERMINANT REDUCTION AND GLOBAL DOMINATION-FAILURE COUNTERCERTIFICATE ARE PROVED. CURRENT FRONTIER = CANONICAL SHELL/DETERMINANT SIGN THEOREM. RH OPEN.**

## Current authority split

```text
live main after theorem PR #137 = fa2f209a6eb8b4059968e8d61239d80588ca256c
live main tree = e3de4dc0377f0124832822b6f97ab5bbd7718640

theorem-state anchor = PR #137 merge fa2f209a6eb8b4059968e8d61239d80588ca256c
validated theorem head = 64988e142590c82bd0ad43604279ede9a8e85eff
theorem tree = e3de4dc0377f0124832822b6f97ab5bbd7718640
RHRC #878 = SUCCESS
Permansson #651 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

Live GitHub head + exact Lean/CI build closure remain authoritative.

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
off-line zero -> domination failure                              PROVED / #137
off-line zero -> q_c<0 OR exists Δ<0                             PROVED / #137
```

## Exact #136/#137 source objects

For the canonical one-step block:

```text
A = intrinsic predecessor block
c = intrinsic cubic shell
b = P_W T c
q_A(w) = Re<Aw,w>
q_c = Re<Tc,c>
Δ(w) = q_c*q_A(w) - |<w,b>|^2.
```

#136 provides scalar-sensitive self-energy and the exact pole/arch/scalar/prime channel decomposition. #137 extends the source bookkeeping to the exact complex pairing and therefore to the exact determinant.

`canonicalOneStepDomination` is exactly

```text
q_c >= 0
AND
forall w, Δ(w) >= 0.
```

This is a proposition, not a proved property of the canonical source.

## Exact global first-bad endpoint

A hypothetical off-critical-line zeta zero forces one finite problem with:

- positive aperture;
- global least-bad successor size;
- both predecessor parity sectors nonnegative;
- an exact negative explicit Schur/eigenvalue root;
- the already-proved zero-shift/source package;
- failure of `canonicalOneStepDomination`;
- therefore the explicit finite sign witness

```text
q_c < 0
OR
exists w in W, Δ(w) < 0.
```

This is the sharp current reduction. No branch of that disjunction has been excluded.

## Current route — canonical shell/determinant signs

**OPEN / DECISIVE ARITHMETIC TARGET.**

Under the exact first-bad-compatible source hypotheses, prove

```text
q_c >= 0
Δ(w) >= 0 for every w in W.
```

The proof must use the actual canonical source normalization. The preferred discovery order is:

1. **falsification:** search canonical low-dimensional predecessor-nonnegative states for `q_c<0` or `Δ<0`;
2. **exact algebra:** expand `q_c`, `q_A`, and `b` through pole/arch/scalar/prime channels and simplify before estimating;
3. **representation search:** test whether the full source pairing has a positive Gram/integral representation making `Δ` a Cauchy-Schwarz remainder;
4. **quantitative cancellation:** use boundary-flat high-order source-coordinate cancellation only if it bounds the full determinant;
5. **formal sign theorem:** theoremize the surviving source-specific mechanism in both parities.

## Why this is not merely a solved Schur problem

#137 proves that domination is sufficient and that an off-line zero forces its failure. It does **not** prove domination. With a nonnegative predecessor and one-dimensional shell, the domination inequalities encode essentially the missing positivity of the one-step extension.

The value of #137 is localization: any hypothetical failure is now forced into a concrete canonical shell-energy or two-dimensional determinant witness.

## Countermodel firewall

Exact rational generic centered-grid reversal-symmetric fixtures already show that Hermitianity, first-bad minimality, parity, KKT, rank-one defect, cross-parity transfer, factor nonvanishing and scalar-shift-invariant data are insufficient.

The new A4b2b route is **not** a revival of those generic dead routes because its premise is the exact canonical source pairing and absolute scalar normalization introduced in #136/#137.

A canonical low-dimensional sign failure would falsify this route but would not be a zeta/RH counterexample unless the exact global-first-bad hypotheses and realizability are separately established.

## A4R fallback

Frozen-cutoff log-lift/dense regular-aperture selection remains available only if it simplifies the source sign proof. Positive-definite predecessors do not themselves exclude a negative successor, and #137 already shows domination would remove resonance without this detour.

## Permanent normalization / claim firewalls

- canonical sign-sensitive object is `canonicalSourceMatrix` under the repaired source convention;
- legacy `finiteMatrix` differs by a scalar identity and cannot supply absolute sign automatically;
- `canonicalOneStepDomination` is OPEN;
- conditional negative-root exclusion is not unconditional exclusion;
- `q_c<0 OR exists Δ<0` is a forced witness, not a contradiction;
- individual source atoms can be indefinite;
- D is algebraic, not unitary/isometric;
- no `A^-1` at zero;
- no division by unproved transfer factors;
- generic countermodels do not refute the canonical source;
- numerical precision is not theorem authority;
- RH remains OPEN.

Detailed current implications and falsification plan: `../../RESEARCH_LEADS_POST_137_DELTA.md`.

**RH remains OPEN.**

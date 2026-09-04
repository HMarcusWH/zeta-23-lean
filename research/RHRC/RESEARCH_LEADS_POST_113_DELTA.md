# Research leads — post-PR #113 delta

> **RH remains OPEN.**

This file is the current post-green research delta after theorem-bearing PRs #112 and #113. It supersedes `RESEARCH_LEADS_POST_110_DELTA.md` for current execution, while the older delta remains a historical record of what was visible after #110.

## Authority

~~~text
main/theorem-state anchor = d3b62817711c4c97f0d817c8b4a4ac0bc646d733
validated theorem head = 2da46eed0068613d904bc67e20790f46bc46818e
theorem tree = 066f5f51041b302dfa1a66d84a024660a09acbf5
merged through = PR #113
RHRC #761 = SUCCESS
Permansson #534 = SUCCESS
CCM build = SUCCESS
ExceptionalZero build = SUCCESS
normalization/source firewall = SUCCESS
forbidden-placeholder gate = SUCCESS
RH = OPEN
~~~

The validated #113 theorem head and the merged #113 tree are identical. Compiler/CI evidence is the authority for the theorem claims below.

## What became formally true

### PROVED — PR #112 / FIRST-BAD-RIGIDITY-D1

- global first badness is available via `AnyParityBad`: a hypothetical off-line zero forces a least globally bad finite size rather than merely a least bad size for one selected parity;
- both parity sectors are nonnegative at every smaller size, in particular at the predecessor size of the global first bad problem;
- the centered predecessor image is internalized as `intrinsicParityPredecessorSubspace` inside the exact successor parity-constrained carrier;
- the one-step shell is internalized as `intrinsicParitySuccShell` and has complex finrank one;
- predecessor plus intrinsic shell spans the successor carrier;
- the first-bad negative eigenmode has a decomposition with a genuinely nonzero intrinsic shell component;
- the cubic parity defect admits a canonical scalar functional `cubicDefectFunctional` and exact pointwise factorization

~~~text
F_N(v) = cubicDefectFunctional(L,N)(v) • oddCubicCompressionVector(N)
~~~

  for the nontrivial finite sectors;
- the cubic generator is nonzero for `N>=2`;
- the cubic generator can be pulled back through the algebraic even/odd D-equivalence and remains nonzero;
- the ExceptionalZero endpoint packages global first badness, predecessor nonnegativity, KKT, intrinsic one-dimensional shell and exact cubic factorization at the same finite problem forced by an off-line zero.

The scalar defect functional is **not** proved nonzero. Exact factorization therefore does not imply exact rank one.

### PROVED — PR #113 / FIRST-BAD-RIGIDITY-D2

- intrinsic predecessor and intrinsic successor shell are disjoint and complementary;
- there is a canonical complex-linear direct-sum equivalence

~~~text
W × S ≃ V;
~~~

- canonical predecessor and shell projections are available as `intrinsicPredecessorPart` and `intrinsicShellPart`;
- every successor vector reconstructs exactly from its two canonical coordinates;
- the canonical shell coordinate vanishes exactly on the intrinsic predecessor:

~~~text
intrinsicShellPart p N v = 0  <->  v ∈ intrinsicParityPredecessorSubspace p N;
~~~

- shell and predecessor are orthogonal in the ambient Euclidean inner product;
- the genuine first-bad negative eigenmode has nonzero **canonical** shell coordinate;
- the projected predecessor block

~~~text
A = P_W T|_W
~~~

  is defined without assuming that W is invariant under T;
- predecessor nonnegativity descends to the self-inner form of A;
- for every real `lam<0`, the safe shifted block `A-lam I` is injective and, by finite dimensionality, bijective;
- the corresponding shifted resolvent is defined;
- a negative eigenmode with canonical decomposition `v=w+s` satisfies

~~~text
(A-lam I) w = -B s,
w = -(A-lam I)^(-1) B s;
~~~

- the eigenvalue equation reduces to the basis-free scalar shifted Schur identity

~~~text
<Ts,s> - lam <s,s> - <(A-lam I)^(-1) B s, B s> = 0;
~~~

- the ExceptionalZero endpoint packages this D2 block reduction at the **same global-first-bad finite problem** as #112's exact KKT and cubic factorization.

## What changed

The post-#110 state contained two promising one-dimensional phenomena but they were not yet fully composable:

~~~text
N-flow side:  an ambient successor shell / non-inherited negative mode
parity side:  a rank-at-most-one compressed defect through g_N
~~~

After #112/#113 the state is stronger:

~~~text
N-flow side:
  native successor carrier V
  canonical orthogonal decomposition V = W ⊕ S
  dim_C S = 1
  genuine negative mode has shell coordinate s != 0
  shifted predecessor coordinates are solved exactly from s
  scalar Schur identity on s

parity side:
  explicit nonzero generator g_N
  exact factorization F_N(v) = ell_N(v) g_N
  algebraic pullback of g_N to the even carrier
~~~

A hypothetical off-line zero is therefore forced into one finite state carrying **three simultaneous compressions**:

1. a one-dimensional N-flow shell;
2. a one-dimensional parity-defect channel;
3. a scalar shifted Schur equation.

This does not solve RH, but it materially shrinks the admissible counterexample state.

## Upstream implications

### U-113-01 — canonical first-bad coordinate API

**Status: DERIVED / engineering recommendation.**

Downstream first-bad proofs should prefer `intrinsicPredecessorPart` and `intrinsicShellPart` over existential predecessor-plus-shell decompositions. The zero-iff-predecessor theorem is especially useful because many future shell-incidence statements can be reduced to membership/non-membership statements.

### U-113-02 — projected predecessor symmetry

**Status: DERIVED / OPEN FORMALIZATION.**

The full parity-compressed canonical operator is symmetric. The shell is orthogonal to W, and A is obtained by projecting T back to W. This should imply

~~~text
<A w1, w2> = <w1, A w2>.
~~~

Prove this directly in the native W carrier. Do not assume W is invariant under T.

### U-113-03 — shifted coercivity

**Status: DERIVED / OPEN FORMALIZATION.**

With A nonnegative and symmetric, for real `lam<0` expect the quantitative estimate

~~~text
Re <(A-lam I)w,w> >= (-lam) ||w||^2.
~~~

This is stronger than the injectivity theorem used by #113 and should support positivity of the shifted resolvent and a norm bound of order `1/(-lam)`.

### U-113-04 — negative index exactly one

**Status: DERIVED / OPEN FORMALIZATION / OPTIONAL.**

At first badness, the form is nonnegative on the codimension-one predecessor W and negative somewhere in V. Standard finite-dimensional geometry therefore strongly suggests negative index exactly one and a unique negative eigendirection. Formalize if Mathlib exposes a clean route; do not let this optional theorem block the more informative shell/cubic composition.

## Downstream implications

### D-113-01 — scale-free one-dimensional secular equation

**Status: READY / OPEN FORMALIZATION.**

Because the actual shell coordinate `s` is nonzero, divide the #113 identity by `<s,s>` and package a shell-line invariant equation. Schematically

~~~text
Phi(lam; [s]) = c_s - lam - r_lam(s) = 0,
~~~

where

~~~text
c_s = <Ts,s>/<s,s>,
r_lam(s) = <(A-lam I)^(-1)Bs, Bs>/<s,s>.
~~~

Prove invariance under replacement `s -> c • s` with `c != 0`.

### D-113-02 — shifted resolvent monotonicity

**Status: LEAD / OPEN FORMALIZATION.**

Once the symmetry/coercivity interface is available, use a resolvent identity rather than differentiation if that is Lean-cheaper. The expected scalar correction

~~~text
r_lam = <(A-lam I)^(-1)b,b>
~~~

should be monotone for negative real lam. This may imply the scalar secular function has at most one negative root.

**Firewall:** uniqueness of a negative root is not absence of a negative root and therefore is not an RH contradiction.

### D-113-03 — parity nullity difference

**Status: DERIVED / OPEN FORMALIZATION.**

The same-space algebraic parity defect has rank at most one. Standard finite-dimensional rank/nullity inequalities should imply a parity nullity-difference bound of at most one at each scalar after algebraic conjugation. The proof must remain algebraic; do not use Hermitian rank-one interlacing because D is not unitary.

### D-113-04 — resonance / one-channel-resolvent dichotomy

**Status: DERIVED / HIGH INFORMATION GAIN.**

For an even eigenmode, exact parity factorization gives

~~~text
(T_- - lam I)(D v) = ell_N(v) g_N.
~~~

If `lam` is not an odd eigenvalue, `D v` is forced into the single opposite-parity resolvent channel generated by `g_N`. If `lam` is simultaneously resonant in both parity sectors, that branch must be classified separately.

The next obstruction should therefore be phrased as a counterexample-space dichotomy rather than as generic positivity.

## Highest-value composition lead: cubic channel versus intrinsic shell

### C-113-A — cubic-shell incidence

**Status: LEAD / HYPOTHESIS — HIGHEST PRIORITY.**

At the same finite first-bad problem we now have:

~~~text
S_N     = intrinsic one-step N-flow shell, dim_C S_N = 1
g_N     = nonzero cubic parity-defect generator.
~~~

The #113 zero-iff-predecessor theorem changes the proof strategy. To show a candidate cubic vector has nonzero shell coordinate, it is enough to show that vector is **not in the centered predecessor image**.

For the odd sector, target the theorem

~~~text
oddCubicCompressionVector (N+1) ∉ intrinsicParityPredecessorSubspace .odd N
~~~

in the appropriately coerced successor carrier, and conclude

~~~text
intrinsicShellPart .odd N (cubic vector) != 0.
~~~

For the even sector, use the algebraic pullback of the cubic generator through D and prove the corresponding non-membership. No metric property of D is allowed.

### C-113-B — explicit outer-coordinate route

**Status: LEAD / HYPOTHESIS / MUST BE FALSIFIED BEFORE PROMOTION.**

The exact odd normal space is `span{d}` and the cubic generator is the orthogonal projection of `d^3` into the odd boundary-flat sector. This suggests the exact form

~~~text
g_K = d^3 - alpha_K d,
alpha_K = <d,d^3>/<d,d>.
~~~

On the centered grid `-K,...,K`, elementary power sums suggest

~~~text
alpha_K = (sum k^4)/(sum k^2)
        = (3 K^2 + 3 K - 1)/5,

(g_K)_(+K)
  = K^3 - alpha_K K
  = K(K-1)(2K-1)/5.
~~~

For `K>=2` the outer coefficient is nonzero. A centered predecessor zero-extension has zero on the newly introduced outer coordinates, so the formula would immediately prove non-membership in W.

This calculation is **not yet theorem-backed**. It must be checked against the exact `orthogonalProjectionOnto` normalization, complex inner-product convention, indexing and successor-size convention before use.

### C-113-C — one-dimensional shell composition

**Status: DERIVED CONDITIONAL ON C-113-A / OPEN FORMALIZATION.**

If the cubic vector has nonzero canonical shell coordinate, then its shell coordinate and the negative eigenmode shell coordinate are two nonzero vectors in the same one-dimensional complex space. Hence there exists `beta != 0` with

~~~text
s_eigen = beta • s_cubic.
~~~

The #113 Schur identity is homogeneous of degree two in the shell vector. The scalar `beta` therefore cancels after normalization. This would replace the arbitrary first-bad shell coordinate by a **canonical cubic-shell direction** and produce the first direct composition of the N-flow and parity-defect channels.

### C-113-D — cubic-normalized Schur rigidity

**Status: LEAD / HYPOTHESIS.**

After C-113-C, target a scalar first-bad equation attached to the canonical cubic shell line. Then combine:

- KKT normal-channel identities;
- exact parity defect coefficient;
- shifted predecessor resolvent;
- possible resolvent monotonicity;
- parity resonance/nullity restrictions.

The goal is not to assume positivity, but to determine whether a globally first-bad negative state satisfying **all** of these constraints can exist.

## Resurrected routes

### Shifted Schur/Feshbach

**Status: PROVED AT THE SAFE FIRST-BAD REDUCTION LEVEL.**

The historical route was unsafe when it used an ambient/coordinate shell and risked `A^-1` at a semidefinite predecessor. #112/#113 remove both problems: the shell is intrinsic and the inverse is only taken at `A-lam I` for `lam<0`.

The route is no longer “derive a Schur equation”; the new question is how much CCM-specific structure can be inserted into the scalar equation.

### Global first-bad comparison

**Status: ACTIVE.**

#112 upgrades fixed-parity least badness to a global least-bad finite size with both predecessor parities nonnegative. This gives a cleaner common state for comparing even/odd resonance than the older selected-parity endpoint.

### Counterexample-space attack

**Status: ACTIVE.**

Do not require a global finite positivity theorem as the next move. Continue shrinking the state a hypothetical off-line zero would be forced to occupy:

~~~text
off-line zero
 -> global first bad finite state
 -> both predecessor parities nonnegative
 -> one-dimensional intrinsic shell
 -> negative shell coordinate != 0
 -> scalar shifted Schur equation
 -> exact one-dimensional cubic parity defect
 -> cubic-shell incidence ?
 -> common resonance OR one opposite-parity resolvent channel
 -> classify / exclude remaining state ?
~~~

## Falsification checks

1. **Projection formula may be wrong.** Derive `g_K=d^3-alpha_K d` from the exact repository projection; do not infer it from parity alone.
2. **Index shift may be wrong.** Carefully distinguish predecessor N, successor N+1 and the argument supplied to `oddCubicCompressionVector`.
3. **Outer coefficient criterion requires exact centered zero extension.** Verify the predecessor image really vanishes on the relevant new outer coordinates in the exact Euclidean carrier.
4. **D is not unitary.** The even pulled-back cubic route may use linear equivalence and coordinate identities only; no norm, angle, spectrum or inertia transfer through D without a separate theorem.
5. **Generator nonzero is not functional nonzero.** `g_N != 0` and exact `F_N=ell_N g_N` still permit `ell_N=0` identically.
6. **Nonzero shell projection is not pure shell.** The cubic vector may have a large predecessor component.
7. **Schur identity is generic.** Ordinary Hermitian block matrices with a negative eigenvalue satisfy such identities; the contradiction must come from additional CCM structure.
8. **At-most-one negative root is not zero negative roots.** Resolvent monotonicity is useful compression, not RH.
9. **Simultaneous parity resonance may occur.** Treat it as a branch to classify, not as impossible until theorem-backed.
10. **No hidden RH-equivalent arithmetic estimate.** Keep the known R001 prime-side equivalence firewall and do not smuggle RH strength into an auxiliary bound.

## Highest-leverage next moves

1. **E1 — cubic-shell incidence.** Prove or falsify the explicit cubic projection/outer-coordinate formula, then theoremize non-membership in W and nonzero canonical shell coordinate for the odd channel; do the algebraic even pullback analogue.
2. **E1b — one-dimensional shell identification.** Prove the cubic shell coordinate and first-bad negative-mode shell coordinate are nonzero scalar multiples.
3. **E2 — cubic-normalized Schur equation.** Transfer #113's scalar identity to the canonical cubic shell line and make it scale-free.
4. **E3 — predecessor block symmetry and shifted coercivity.** Strengthen the resolvent interface and seek positivity/norm/monotonicity statements for negative shifts.
5. **E4 — nullity/resonance-resolvent theorem.** Formalize the algebraic parity nullity bound and the common-resonance versus one-channel-resolvent dichotomy.
6. **Falsify simultaneous resonance.** Use displacement/KKT/cubic/shell structure before investing in a much larger global positivity proof.
7. Keep `G1-B1B -> G1-final -> S-NEG -> G23` alive as the independent source-faithful lane.

## Standing questions after #113

**Given everything now formally true, what becomes possible that was not possible before?**

The shell-versus-cubic comparison can now be reduced to a predecessor **non-membership** theorem because #113 gives canonical shell coordinates and the exact zero-iff-predecessor characterization. The Schur/Feshbach route itself is no longer hypothetical; it is theorem-backed at first badness.

**If this contains a clue toward RH, where does it propagate?**

Upstream, it suggests a canonical block/resolvent API on W. Downstream, it suggests replacing the arbitrary shell coordinate by a cubic-generated shell line and composing the scalar Schur equation with the exact parity-defect coefficient and resonance constraints.

**What experiment or lemma most efficiently tests whether the clue is real?**

Prove or falsify the exact outer coefficient of `oddCubicCompressionVector K` and use it to decide membership in the centered predecessor image. This is a small, adversarially checkable theorem with high information gain.

**RH remains OPEN.**

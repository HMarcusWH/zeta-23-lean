# Research leads — post-PR #100 delta

> **RH remains OPEN.**

## Authority

~~~text
PR #100 final validated head = 497adcd6a746d49fd23654cabf4ed8f0c58db8a9
PR #100 merge = 4427e2a8c8d90dbb7d66d9d96f9a410cecb75df9
validated/merged theorem tree = 705ab8b88728a5b90d850eb4b51c01a66811f088
RHRC #691 = SUCCESS
Permansson #464 = SUCCESS
CCM build = SUCCESS
ExceptionalZero build = SUCCESS
forbidden-placeholder gate = SUCCESS
axioms = [propext, Classical.choice, Quot.sound]
sorryAx = absent
~~~

## What became formally true

**PROVED / PR #100**

For N<=M the correct centered embedding shifts Fin coordinates by M-N and preserves centeredIndex exactly. The embeddings compose coherently.

The canonical source matrices satisfy exact central principal-block nesting.

Raw centered zero extension preserves every centered moment, not only the three boundary-flat constraints, and preserves the represented localized finite function exactly.

The Euclidean/PiLp₂ centered zero extension is a linear isometry, transports the Euclidean boundary-flat constrained sector to every larger centered truncation, and preserves the canonical real inner-self value.

The exceptional-zero endpoint is upgraded to:

~~~text
off-line zero
  -> exists fixed L>0 and N0>=2
  -> for every M>=N0
     exists nonzero x_M in euclideanBoundaryFlatSubspace M
     with Re <M_M(L)x_M,x_M> < 0.
~~~

No parity theorem, constrained compression, negative constrained eigenmode, positivity theorem, finite-to-infinite theorem or RH theorem is proved.

## What changed

PR #98 supplied one finite constrained Euclidean negative direction.

PR #100 turns that isolated obstruction into a coherent fixed-aperture tail of finite constrained negative problems. The truncation size can no longer be treated as an accidental one-off parameter: once a bad constrained direction exists at fixed L, the same quadratic value survives in every larger centered truncation.

Lean also exposed a more general structure than the roadmap requested: all centered moments and the finite represented function are preserved under extension.

## Upstream implications

**DERIVED / OPEN FORMALIZATION**

The #100 all-moment theorem suggests a reusable generic moment-flag nesting API: any finite system defined by finitely many centered-moment equations should transport under the same centered extension.

A high-value compatibility theorem should be tested:

~~~text
D_M (E_{N,M} u) = E_{N,M} (D_N u)
~~~

where D is the centered-index operator. If true, its iterates would make the finite Krylov/moment flag coherent across N and connect #100 directly to the #96 displacement/Hankel package.

A purely finite proof of canonical quadratic preservation may remove the current hL>0 assumption inherited from the G1-A proof route. This is cleanup/generalization, not required for the fixed-aperture exceptional-zero endpoint.

## Downstream implications

**DERIVED / OPEN FORMALIZATION**

For fixed L define:

~~~text
Bad_L(N) :=
  exists nonzero x in V_N,
    Re <M_N(L)x,x> < 0.
~~~

PR #100 gives:

~~~text
N <= M and Bad_L(N) -> Bad_L(M).
~~~

Therefore any nonempty bad-size set has a least global bad size N*. Parity is not required for existence of this global first bad N.

From PR #98:

~~~text
finrank V_N = 2*N-2.
~~~

Together with the #100 isometric embedding into V_(N+1), the total orthogonal new constrained shell has finrank two.

After parity dimensions are theorem-locked, this 2D increment is expected to split into one even and one odd dimension. That creates the intended one-dimensional first-bad parity shell.

## Resurrected routes

The exact finite algebraic core of historical FTI-C1 survives its kill condition: exact centered principal-block nesting is true.

What remains dormant is the historical finite-to-infinite convergence layer. PR #100 does not prove topology, determinant convergence, closure, pole control, zero transfer or an infinite limiting theorem.

The secular/Schur route is also revived in a cleaner constrained form: first a 2D global constrained shell, then potentially a 1D parity shell. This shell is not automatically the old ambient coordinate shell.

## New RH-relevant clues

### LEAD — monotone constrained Rayleigh bottom

Once the constrained symmetric operator is built, #100 supplies the variational ingredients needed for:

~~~text
lambda_min(L,M) <= lambda_min(L,N)  whenever N <= M.
~~~

The reason is isometric inclusion plus exact quadratic-value preservation, not literal operator nesting.

A hypothetical off-line zero would then force a fixed-L finite spectral sequence whose bottom value is eventually negative.

### LEAD — first bad finite spectral crossing

Combining global first bad N with constrained spectral extraction should produce a first truncation where the constrained Rayleigh bottom becomes negative while the entire previous constrained space is nonnegative.

That localizes the first failure to the 2D new constrained shell; after parity, to a 1D shell.

### LEAD — parity/displacement collapse

If reversal proves displacementVector odd, the displacement pairing with an even vector should cancel under reversal. Combined with the #96 constrained commutator identity, this may force a stronger even-sector commutator collapse.

This is only a lead until the reversal and oddness theorems are proved.

## Falsification checks

- Exact principal-block nesting does **not** imply M_M E = E M_N.
- Exact quadratic preservation does **not** imply literal nesting of the orthogonally compressed operators.
- Global first-bad existence is generic well-ordering plus #100 persistence; by itself it is not an RH-level obstruction.
- A 2D or 1D shell may yield only an ordinary secular equation with no arithmetic contradiction.
- All-moment preservation is strong infrastructure but may be generic centered-support geometry rather than a special zeta rigidity.
- No finite-to-infinite route should be reactivated without explicit topology/norm/closure/pole-control theorems.
- No positivity theorem may be assumed merely because the nested family is symmetric/Hermitian.

## Highest-leverage next moves

1. **PARITY:** centered-index reversal, embedding/reversal compatibility, simultaneous matrix reversal invariance, moment parity, displacement oddness, constrained-sector invariance, exact even/odd dimensions.
2. **GLOBAL FIRST BAD:** theorem-lock Bad_L upward closure, least bad N and total 2D constrained shell.
3. **K0-F1F:** build constrained orthogonal compression, prove symmetry and extract a negative constrained eigenmode.
4. **PARITY FIRST BAD:** refine to a one-dimensional new parity shell.
5. **KKT:** prove V_N^perp = span_C {1,d,d²}.
6. **SECULAR/DISPLACEMENT:** derive the scalar parity-shell equation and compose it with the exact displacement/Krylov structure.
7. **K1 IF NEEDED:** only then open aperture continuity, positive anchor, first crossing and prime-event jump structure.

## Standing question

Given everything now formally true, the most efficient next test of whether the finite-wall clue is real is the parity package.

If parity produces the expected exact 1+1 constrained growth and the displacement vector has the expected odd symmetry, the hypothetical counterexample state becomes substantially more rigid. If either fails, the route should be revised immediately rather than RH-fitted.

**RH remains OPEN.**

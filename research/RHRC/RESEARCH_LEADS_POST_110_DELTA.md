# Research leads — post-PR #110 delta

> **RH remains OPEN.**

## Authority

~~~text
main/theorem-state anchor = 07e0c845d128831b244b13503c9640b934bf4416
validated theorem head = ca0c389827520e2005390637742389819dc97068
theorem tree = f2e9985ac976c83ecfa7f5dbce64b1e0193680b0
merged through = PR #110
RHRC #738 = SUCCESS
Permansson #511 = SUCCESS
CCM build = SUCCESS
ExceptionalZero build = SUCCESS
normalization/source firewall = SUCCESS
forbidden-placeholder gate = SUCCESS
#109 printed axiom surface = [propext, Classical.choice, Quot.sound]
#110 theorem-specific promoted axiom surface = revalidated by this control-plane PR
RH = OPEN
~~~

## What became formally true

**PROVED — PR #109:**

- the #107 first-bad negative eigenmode has nonzero orthogonal projection onto the already-proved one-dimensional ambient Euclidean successor parity shell;
- predecessor nonnegativity is available directly on the embedded predecessor image in the successor ambient matrix;
- exact parity normal spaces:
  - even `(V+)ᗮ ∩ E+ = span{1,d²}`;
  - odd `(V-)ᗮ ∩ E- = span{d}`;
- every parity-compressed eigenmode has the corresponding exact KKT residual;
- a hypothetical off-line zero forces a fixed-aperture fixed-parity least-bad negative eigenmode with predecessor nonnegativity, nonzero one-dimensional shell projection and exact KKT residual.

**PROVED — PR #110:**

- Euclidean centered-index restriction `D : V_N^+ -> V_N^-` is injective, and for `N>=1` an algebraic complex-linear equivalence;
- arbitrary even compression residual lies in `span{1,d²}`;
- the canonical Euclidean operator satisfies `M(Du)=D(Mu)` on the even constrained sector;
- the explicit odd cubic channel `g_N=P_-d³` is nonzero for `N>=2`;
- every compressed intertwining defect value is a scalar multiple of `g_N`;
- `range(T_-D-DT_+) <= C g_N`;
- the even-to-odd defect has complex finrank at most one;
- after algebraic conjugation of the odd compression back to the even carrier, the same-space parity defect also has complex finrank at most one.

## What changed

The post-#107 lead predicted that parity KKT plus the exact even commutator collapse should expose a projected `d³` defect. That prediction has now survived formalization.

The hypothetical off-line-zero obstruction has therefore been compressed twice:

~~~text
N-flow compression:
  first bad state = nonnegative predecessor + one new complex shell direction

parity compression:
  even/odd compressed dynamics differ through at most one explicit cubic channel
~~~

This is stronger than merely having a finite negative eigenmode. The remaining counterexample state is increasingly forced into scalar channels.

## Upstream implications

1. The old post-#107 task “prove nonzero shell projection” is retired: #109 proves it in the ambient Euclidean formulation.
2. The old task “prove parity-specific normal spaces / KKT” is retired: #109 proves both.
3. The old lead “inspect the projected d³ defect” is promoted: #110 proves the operator-level one-line range theorem.
4. The remaining shell task should be stated precisely as **intrinsic successor-subtype block geometry**, not as if the shell itself were still unproved.
5. Negative-index-one / unique negative eigenline remains optional formalization; it should not block the shifted scalar calculation.

## Downstream implications

### D-110-01 — shifted first-bad Schur/Feshbach equation

**Research status:** READY / HIGHEST PRIORITY  
**Formal status:** OPEN

At the first bad successor, the predecessor sector is nonnegative and the distinguished eigenvalue satisfies `lam<0`. Therefore the safe predecessor shift is

~~~text
A - lam I > 0
~~~

and should be invertible even if `A` has kernel at zero.

Target scalar identity:

~~~text
c - lam - b* (A - lam I)^(-1) b = 0.
~~~

This must be derived in the native successor-subtype block decomposition. Do not use `A^-1` at zero.

### D-110-02 — explicit rank-one defect factorization

**Research status:** READY  
**Formal status:** LEAD / HYPOTHESIS

#110 proves only

~~~text
range F_N <= C g_N,
finrank(range F_N) <= 1.
~~~

Try to theoremize an explicit linear functional `ell_N` with

~~~text
F_N v = ell_N(v) • g_N.
~~~

If `ell_N` can be made canonical and proved nonzero, this upgrades the current rank-at-most-one result to an actual one-channel operator identity.

### D-110-03 — parity nullity-difference bound

**Research status:** READY  
**Formal status:** DERIVED / OPEN FORMALIZATION

Let

~~~text
B_N = E^-1 T_- E
~~~

on the even carrier. #110 proves `rank(B_N-T_+)<=1`. Standard finite-dimensional rank/nullity inequalities therefore suggest

~~~text
|dim ker(B_N-zI) - dim ker(T_+-zI)| <= 1
~~~

for every scalar `z`.

Because `B_N` is algebraically conjugate to `T_-`, this becomes an even/odd parity nullity-difference bound. The theorem should be proved algebraically; do not invoke Hermitian rank-one interlacing because E is not unitary.

### D-110-04 — common-resonance vs one-channel-resolvent dichotomy

**Research status:** READY / HIGH INFORMATION GAIN  
**Formal status:** DERIVED / OPEN FORMALIZATION

For an even eigenvector `T_+ v = lam v`, #110 gives

~~~text
(T_- - lam I) (D v) = F_N v ∈ C g_N.
~~~

If `lam` is not an odd eigenvalue, then formally

~~~text
D v ∈ C (T_- - lam I)^(-1) g_N.
~~~

Thus a candidate first-bad mode is forced into one opposite-parity resolvent channel unless the two parity sectors are simultaneously resonant at `lam`.

This sharpens the next obstruction to:

> can a first-bad canonical state support the required simultaneous even/odd resonance?

### D-110-05 — cubic channel versus first-bad N-flow shell

**Research status:** TESTING / HIGH VALUE  
**Formal status:** LEAD / HYPOTHESIS

There are now two proved one-dimensional structures:

1. the first-bad successor shell from N-flow;
2. the parity defect channel generated by `g_N=P_-d³`.

Pull the cubic channel back through the algebraic D-equivalence:

~~~text
h_N = E^-1 g_N.
~~~

Test whether the projection of `h_N` onto the first-bad successor shell is nonzero.

A useful explicit route is to compute the odd projection of `d³`. Since the odd normal is `span{d}`, one expects

~~~text
g_N = d³ - alpha_N d,
alpha_N = <d,d³>/<d,d>.
~~~

Then `h_N` is morally the even vector `d²-alpha_N` on the constrained sector. If its outer centered coefficient is nonzero, it cannot lie in the centered predecessor image, hence it has nonzero component in the one-dimensional successor shell.

This is a promising composition clue, not yet a theorem. It must be checked carefully against the actual projection normalization and subtype coercions.

## Resurrected routes

### Shifted Schur/Feshbach

**Status:** RESURRECTED / ACTIVE.

The old ambient-coordinate Schur route was unsafe because it conflated the historical coordinate shell with the constrained parity shell. #105/#107/#109 now provide the correct constrained first-bad geometry; the remaining obligation is to build the intrinsic successor-subtype block decomposition before applying the shifted formula.

### Global first-bad comparison

**Status:** READY FOR REASSESSMENT.

Fixed-parity least badness was previously the cleanest reduction. After #110, the two parity compressions at the same N are linked by an algebraic rank-at-most-one defect. A global first-bad size may therefore carry extra information because both parity sectors are nonnegative at the predecessor. Reassess whether this gives a cleaner simultaneous-resonance exclusion than working with one selected parity alone.

## New RH-relevant clues

### C-110-A — two scalar bottlenecks may compose

**LEAD / HYPOTHESIS.**

A hypothetical off-line zero now forces a first bad state whose new N-flow content is one-dimensional, while the even/odd compression mismatch is also one-dimensional. If these lines couple nontrivially, the finite obstruction may reduce to a single scalar secular condition plus one scalar parity-defect coefficient.

### C-110-B — attack resonance rather than positivity directly

**LEAD / HYPOTHESIS.**

Instead of trying immediately to prove every canonical finite matrix positive, attack the counterexample state:

~~~text
hypothetical off-line zero
  -> first bad negative eigenmode
  -> nonzero new shell component
  -> rank-one parity defect
  -> common parity resonance OR one resolvent channel.
~~~

If common resonance can be excluded from the arithmetic/displacement structure, the admissible counterexample space collapses sharply without first proving a global positivity theorem.

## Falsification checks

- `finrank <= 1` may be rank zero.
- `g_N != 0` does not prove the defect functional is nonzero.
- algebraic D-equivalence is not unitary; ordinary Hermitian rank-one interlacing is unavailable without a transported metric.
- the conjugated odd compression need not be self-adjoint in the original even-sector inner product.
- nonzero projection to the one-dimensional N-flow shell does not make the eigenmode a pure shell vector.
- the shell is not proved invariant.
- the expected formula `g_N=d³-alpha_N d` must be derived from the exact orthogonal projection, not guessed from parity alone.
- the pulled-back cubic channel may conceivably lie in the predecessor image; test this before building around the shell-alignment clue.
- simultaneous even/odd resonance may occur and could kill the simple resolvent route.
- the scalar Schur formula must use `A-lam I`, never `A^-1` at a semidefinite predecessor.
- none of these clues is a positivity theorem, finite-to-infinite theorem or RH theorem.

## Highest-leverage next moves

1. **Control-plane sync** — this document and companion registry/binding updates.
2. **Intrinsic block geometry** — predecessor subspace and one-dimensional shell inside successor parity subtype.
3. **Shifted Schur/Feshbach** — prove invertibility of `A-lam I` and the scalar first-bad equation.
4. **Explicit parity defect functional** — factor `F_N` through `g_N`.
5. **Cubic-shell test** — determine whether `E^-1 g_N` necessarily has nonzero first-bad shell component.
6. **Parity nullity theorem** — formalize the rank-one nullity difference.
7. **Resonance/resolvent dichotomy** — make the next obstruction exact.
8. **Falsify simultaneous resonance** using displacement/KKT/arithmetic structure before investing in a larger positivity proof.
9. Keep `G1-B1B -> G1-final -> S-NEG -> G23` alive as an independent source-faithful cross-check.

## Standing questions after #110

**Given everything that is now formally true, what becomes possible that was not possible before?**

A candidate off-line-zero obstruction can now be studied simultaneously through a one-dimensional N-flow shell and a one-dimensional parity-compression defect.

**If this contains a clue toward RH, where does it propagate?**

Upstream it suggests a smaller canonical block abstraction. Downstream it points to a scalar Schur equation and a resonance/resolvent dichotomy rather than an unconstrained spectral search.

**What is the fastest test of whether the clue is real?**

Theoremize or falsify the shell component of the pulled-back cubic channel `E^-1 g_N`, while independently deriving the safe shifted Schur equation.

**RH remains OPEN.**

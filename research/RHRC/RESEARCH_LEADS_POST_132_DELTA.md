# Post-#132 research delta — kernel transport, countermodel firewalls, and absolute canonical energy

Date: 2026-09-09  
Audited main: `38f65ce4abf5eec258d51425e7c9c88b63b21ffb`  
Theorem authority: PR #131  
Documentation/control sync: PR #132  

> **Claim firewall: RH remains OPEN.**

This note records the mathematical state change produced by the post-#132 audit and exact countermodel campaign. It does not add a Lean theorem. Labels below are mandatory.

## What became formally true

No new theorem became true after #131. PR #132 is documentation/control metadata only.

**PROVED through PR #131:**

- hypothetical off-line zero -> one finite global-first-bad state;
- a negative explicit shift `lam<0` is an exact secular/eigenvalue root there;
- both predecessor parity sectors are nonnegative;
- canonical `V=W⊕S`, one-dimensional shell, KKT/cubic geometry and exact zero-shift endpoint;
- `Re S0<0` at the forced negative root;
- exact zero-shift shell response and `Re sigma0<0` in the regular branch;
- canonical regular/resonant kernel coordinate and exact resonant pole;
- exact cross-parity secular transfer;
- cubic parity defect = canonical quadratic source moment;
- exact production source-moment decomposition into pole-even, reduced arch diagonal/off-diagonal and finite von-Mangoldt source atoms.

No branch exclusion, negative-root exclusion, terminal RH bridge or RH theorem is proved.

## What changed

The post-#132 audit found that the next highest-information structural theorem is not merely a source-expanded restatement of #129. The stronger object is a denominator-free zero-shift kernel/source transport identity.

At the same time, exact rational countermodels show that increasingly strong factorwise transfer heuristics still do not control absolute spectral sign. The project should therefore transition from generic structural geometry to arithmetic normalization / absolute energy.

## DERIVED — finite kernel/source transport target

Use the even/odd successor spaces `V+`,`V-`, predecessor blocks `A+`,`A-`, centered-index transport `D`, predecessor correction vectors `d`,`a`, source functional `mu`, and shell norms `rho+`,`rho-`.

For every `z in ker A+`, define

```text
beta(z) = <b+,z>/rho+.
```

The existing #129/#131 defect and quotient identities imply the exact targets

```text
A-(Dz) = beta(z) d + mu(z) a
<b-,Dz>/rho- = beta(z) + mu(z).
```

Writing `K+`,`K-` for the orthogonal predecessor-kernel projections and `k+=K+b+`, projection to the entire odd predecessor kernel gives

```text
(||k+||^2/rho+) K-d + mu(k+) K-a = 0.
```

This is stronger than the scalar cancellation that would appear as the leading Laurent-pole cancellation in a future shifted-resolvent expansion. It needs neither a spectral limit nor a pseudoinverse.

## DERIVED — direct zero-shift transfer

Assume only that both predecessor couplings have preimages

```text
A+ x+ = b+
A- x- = b-.
```

Set `u+0=c+-x+` and `u-0=c--x-`. Then the target zero-shift relation is

```text
sigma- = alpha0 sigma+ + Gamma0 mu(u+0)
Gamma0 = <u-0,g->/rho-.
```

Neither whole-block invertibility nor positive definiteness is needed.

Important qualification: the endpoint response is independent of the preimage, but `alpha0` and `Gamma0` individually can change when a preimage is modified by a kernel vector. A future limit from negative shifts selects the kernel-orthogonal preimage; it must not be silently identified with arbitrary preimages.

## DERIVED — overlap/source annihilation on a regular kernel

Under both regular couplings, for every `z in ker A+`,

```text
Gamma0 * mu(z) = 0.
```

Consequences:

- `Gamma0 != 0` forces the source functional to vanish on the entire even predecessor kernel;
- one kernel vector with `mu(z) != 0` forces `Gamma0=0`;
- this is a compatibility dichotomy, not exclusion.

## EXPERIMENTAL SIGNAL — exact rational post-#129 countermodels

Exact rational generic reversal-symmetric diagonal models retain the actual centered grid, boundary-flat parity geometry, first-bad predecessor nonnegativity, KKT extraction, rank-one cubic defect, quotient transport, shifted trial reconstruction, overlap formula and full #129 scalar transfer.

They are not the canonical arithmetic source and not RH counterexamples.

Three decisive mechanisms occur exactly:

```text
1. common negative root with sourceMoment(u+) != 0 but Gamma = 0
2. common negative root with Gamma != 0 but sourceMoment(u+) = 0
3. odd-only negative root with alpha = 0 while the even successor is positive
```

Additional exact fixtures realize negative `Gamma`, negative `alpha`, and either sign of the source moment.

Therefore generic nonvanishing/sign assumptions on `alpha`, `Gamma`, overlap or source moment are not valid structural shortcuts. Even-only root exclusion is insufficient.

## EXPERIMENTAL SIGNAL — canonical numerical checks

High-precision evaluation of the literal canonical source formula gives internally consistent #129 transfer residuals below roughly `1e-60`, including an 80-digit recheck near `1e-81`.

The sampled canonical states include:

- positive source moments;
- a negative source moment at a state with positive predecessor spectra;
- a negative `alpha` in another canonical sample.

These are diagnostic computations, not interval proofs and not counterexamples to a theorem unless the theorem's exact hypotheses are matched and certified.

## DERIVED FIREWALL — scalar-shift origin blindness

For the generic structural package, simultaneously shifting

```text
M -> M+tI
lambda -> lambda+t
```

leaves the shifted predecessor resolvent equations, trial vectors, cubic defect/source functional, `alpha`, `Gamma`, and secular transfer data unchanged while moving the spectrum relative to zero.

Therefore the structural cross-parity package cannot by itself locate the absolute spectral origin.

This explains why #131's quadratic-normal moment is insufficient as the terminal sign observable: it deliberately annihilates scalar identities.

## LEAD — absolute canonical source energy

The next arithmetic observable should retain the canonical scalar normalization:

```text
E(v) = Re<Tv,v>.
```

For a canonical parity compression it should be decomposed as

```text
pole energy
- reduced arch diagonal energy
- reduced arch off-diagonal energy
- canonical arch scalar correction * ||v||^2
- finite von-Mangoldt weighted source-atom energies.
```

For a regular zero-shift trial, this absolute energy is the zero-shift Schur endpoint `S0` (after the exact already-proved identification/orientation is respected).

Unlike the #131 normal moment, this observable remembers where zero is.

## LEAD — canonical one-step domination

The decisive finite theorem is now most cleanly stated as follows.

For either parity, with predecessor `A>=0`, shell vector `c`, coupling `b=P_W T c`, and

```text
q_c = Re<Tc,c>,
```

prove from the actual canonical CCM source

```text
q_c >= 0
|<w,b>|^2 <= q_c * Re<Aw,w>    for every w in W.
```

This is equivalent to positivity of the one-step block extension when `A>=0`. It is unresolved positivity content, not a bookkeeping lemma.

If proved:

1. `w in ker A` forces `<w,b>=0`, hence the coupling lies in `range A` and resonance disappears;
2. in the regular branch choose `Ax0=b`; the domination inequality gives the zero-shift Schur complement `S0>=0`;
3. the existing first-bad theorem gives `Re S0<0` at the forced negative root;
4. contradiction.

Thus one sufficiently strong canonical domination theorem can potentially discharge both regular and resonant branches.

## LEAD — high-order source-coordinate cancellation

Direct Taylor algebra suggests stronger endpoint cancellation than the current formal C2 source-dictionary layer records.

For boundary-flat vectors (`mu0=mu1=mu2=0`), the first potentially nonzero terms at `omega=0` are predicted to be

```text
odd atom energy:
  -2(2pi)^6 |mu3|^2 omega^7 / 7!

even atom energy:
  +2(2pi)^8 |mu4|^2 omega^9 / 9!

even quadratic-normal moment:
  -2(2pi)^6 mu4 omega^7 / 7!
```

High-precision ratios approach one at the predicted orders. These expansions are not Lean theorems. They may supply quantitative control for the absolute-energy/domination estimate; they do not imply global atom positivity.

## LEAD — regular-aperture selection by logarithmic nonidentity

If resonance materially complicates the arithmetic estimate, a separate reduction may select a nearby aperture with positive-definite predecessors.

Freeze the finite prime cutoff and seek an exact decomposition

```text
M_Q(L) = -log(L) I + B_Q(L).
```

With `L=exp(z)`, the matrix remainder becomes periodic under `z -> z+2*pi*i`. A determinant

```text
det(Bhat(z)-zI)
```

cannot vanish identically: periodicity would give one fixed finite matrix too many distinct characteristic roots along a vertical orbit.

After the required holomorphy/real-analyticity and cutoff-continuity proofs, this should yield dense apertures where finitely many predecessor parity compressions are injective. Preserve an existing negative vector by continuity, move to such an aperture, then reselect the least-bad size. Its predecessors are PSD by minimality and injective by selection, hence PD.

This is a simplification theorem only. Exact generic fixtures show that PD predecessors can still coexist with a negative successor root; the canonical energy inequality remains independent mathematical content.

## Upstream implications

- The #131 source-moment decomposition should not be generalized merely by adding more shift-invariant source observables. The missing information is absolute normalization.
- The archimedean scalar correction, intentionally removed from the cubic normal moment, becomes central again in absolute energy.
- A generic Laurent expansion is lower priority because its leading cancellation is already captured by the finite kernel vector identity.

## Downstream implications

If canonical one-step domination is proved for both parities, the downstream chain should be short:

```text
canonical domination
  -> no canonical first-bad negative state
  -> contradiction with the existing off-line-zero -> first-bad theorem
  -> no off-line zero in the project carrier
  -> explicit terminal wrapper to Mathlib RiemannHypothesis.
```

The final statement wrapper remains open and must not be conflated with finite exclusion.

## Resurrected routes

- source-energy analysis is resurrected in a stronger form because #131 now gives exact channel decomposition and the countermodels identify the missing scalar-normalization information;
- aperture variation is worth reconsidering only as a way to simplify resonance, not as a positivity proof;
- high-order source-dictionary regularity becomes relevant because boundary-flat cancellations may feed the needed coercive estimate.

## Falsification checks

Every proposed estimate should be attacked against:

- exact rational post-#129 fixtures;
- `Gamma=0`, `alpha=0`, overlap zero and sourceMoment zero cases;
- both root parities;
- scalar-shift covariance;
- canonical low-dimensional high-precision evaluations;
- the exact elementary source atom at `omega=1/2`, where legal fixtures have both positive and negative energies;
- degenerate higher-moment cases where the predicted leading Taylor coefficient vanishes;
- the distinction between projected predecessor kernel and predecessor-size compressed spectrum.

Never divide by an unproved factor. Never use D as an isometry. Never introduce `A^-1` at zero. Never upgrade numerical residuals or exact generic countermodels into canonical/RH theorems.

## Highest-leverage next moves

1. **Lean PR:** kernel/source transport + full kernel projection + direct zero-shift transfer + regular-kernel overlap/source annihilation.
2. **Lean/source bookkeeping PR:** absolute canonical source-energy decomposition retaining the arch scalar correction.
3. **Discovery + theorem attack:** canonical one-step domination/coercivity in both parities.
4. **Parallel quantitative tool:** formal source-coordinate `omega^7/omega^9` endpoint expansions if they materially support step 3.
5. **Fallback simplifier:** log-lift dense regular-aperture selection if resonance remains an avoidable source of proof complexity.
6. **Only after finite exclusion:** terminal Mathlib RH wrapper.

## Standing questions

Given everything now formally true, the finite reduction is already in place. The central question is:

> What property of the exact canonical pole/arch/prime normalization makes the one-step extension positive whenever its predecessor is nonnegative?

If the high-order endpoint cancellations are the clue, where do they propagate into the absolute energy? If the kernel identity is the clue, what canonical source theorem makes its projected forcing dependence impossible?

The fastest falsifier is a low-dimensional canonical counterexample to a proposed domination estimate. The fastest confirmation is an exact source inequality whose hypotheses visibly fail on the generic scalar-shift countermodels.

**RH remains OPEN.**

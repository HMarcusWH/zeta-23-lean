# Post-#140 research delta — aperture freedom and fixed-cell finite regularization

> **Claim firewall: RH remains OPEN.**

Date: 2026-09-09

This delta supersedes the post-#138 Astra delta as the current-priority research note. The older delta remains historical evidence and should not be rewritten to look current.

## Exact validated authority

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

Compiler/CI evidence is authoritative for the exact theorem state. PR #140 contains theorem-bearing Lean changes and therefore advances the theorem-state anchor beyond #137. It does not change the terminal RH claim.

## What became formally true

### PROVED — aperture freedom from an off-line zero

`Zeta23/ExceptionalZero/ApertureFreedom.lean` proves:

```text
off-line zero
  -> exists L0>0 such that for every L>L0
       there exists a finite boundary-flat canonical vector u
       with Re quadraticForm(canonicalSourceMatrix L N,u) < 0.
```

It also packages:

```text
every sufficiently large aperture -> some AnyParityBad(L,N)

every sufficiently large aperture -> a freshly selected least global-first-bad Nstar.
```

The finite size and negative vector may depend on the chosen aperture.

### PROVED — regularity scaffold

`Zeta23/CCM/CanonicalApertureRegularityScaffold.lean` proves:

```text
IntrinsicPredecessorRegular(p,L,N)
  <-> intrinsicPredecessorBlock(p,L,N) is injective.

regular predecessor
  -> every target has a unique predecessor preimage
  -> in particular the cubic shell coupling has a unique zero-shift preimage.
```

It also theorem-locks:

```text
frozenCanonicalPrimeMatrix Q L K

floor(exp L)=Q
  -> frozenCanonicalPrimeMatrix Q L K = canonicalPrimeMatrix L K

primeSourceCoordinate q (log q)=0
  -> sourceMatrix(...) = 0 at the entry threshold

-2*wCorrection(L)
  = -log(L) + canonicalApertureScalarRemainder(L),  L>0.
```

No theorem proves dense regular apertures, holomorphic continuation of the full production predecessor block, successor positivity, the regular Schur-energy sign, negative-root exclusion, or RH.

## What changed mathematically

The decisive improvement is a quantifier change.

Before #140 the A4R plan had to preserve one already-selected finite witness while moving its aperture. After #140, a hypothetical off-line zero forces fresh finite negativity at **every sufficiently large aperture**.

Therefore the route can choose a convenient aperture first, then obtain a finite bad witness there.

This permits a stronger simplification than the original post-#138 plan.

## New preferred A4R composition — one frozen cutoff cell

Choose `Q` so large that

```text
L0 < log Q.
```

Then choose `L1` strictly inside the physical cutoff cell

```text
log Q < L1 < log(Q+1).
```

On this whole cell:

```text
floor(exp L)=Q,
```

so the prime channel is the fixed finite frozen source sum.

Invoke #140 at `L1`. Obtain some finite `N,u` with strict canonical negativity.

Now `N` is known.

If the fixed-`N,u` energy is continuous in `L` on the cell, strict negativity persists on a small interval `J` around `L1`.

It is then enough to avoid singular predecessor determinants for the **finite family**

```text
p in {even,odd}
1 <= k <= N.
```

If each fixed `(Q,p,k)` regular set is dense in the cutoff cell, the finite intersection is dense. Choose `L2 in J` in that intersection. The same `u` remains negative at `L2`. Then reselect global first-bad at `L2`; its index is at most `N`, so the relevant predecessors are regular by construction.

### Consequence of this planning correction

The primary route no longer needs an all-size Baire-category theorem or countable simultaneous determinant avoidance.

It also does not need to cross a prime/prime-power threshold during the regularizing move.

Threshold continuity remains useful infrastructure but is not load-bearing for the preferred proof.

## Current A4R theorem obligations

For fixed `Q,p,N`, define the determinant of the actual projected predecessor block on the frozen cutoff cell.

The target is:

```text
1. continuity of fixed finite canonical energy in L on one cutoff cell;
2. analyticity/holomorphy of the frozen projected predecessor family;
3. determinant nonidentity for each fixed p,N;
4. dense nonzero-determinant apertures for each fixed p,N;
5. finite simultaneous avoidance through a prescribed finite horizon M;
6. composition with #140 negativity and fresh first-bad reselection.
```

The regularity target must remain the actual `intrinsicPredecessorBlock`, not a predecessor-size proxy.

## Candidate determinant-nonidentity mechanism

The #140 scalar theorem validates the real-axis `-log L` coefficient in `wCorrection`. The remaining task is to expose the corresponding full projected-block decomposition on the frozen source family.

The candidate log-cover argument should be stated carefully:

```text
Ahat(z) = -z I + Rhat(z)
Rhat(z+2*pi*i) = Rhat(z)
```

for a single-valued holomorphic remainder on the lifted frozen-cutoff family.

If `det Ahat` vanished identically, then at one base point `z` the same finite matrix `Rhat(z)` would have the distinct eigenvalues

```text
z, z+2*pi*i, ..., z+2*pi*i*d
```

for `d+1` values in dimension `d`, impossible.

This is a **LEAD / HYPOTHESIS** until the production archimedean continuation and exact block decomposition are proved.

Do not use the invalid shortcut that treats the physical composition `A(exp z)` as simultaneously periodic and equal to `-z I + periodic` without a genuine log-cover continuation.

## Resurrected route — old dictionary archimedean machinery

The A4R analytic obligation should first reuse the existing theorem-backed dictionary/gamma infrastructure before adding new parameter-dependent integral machinery.

Relevant files include:

```text
Zeta23/CCM/DictionaryArchPhysical.lean
Zeta23/CCM/DictionaryArchBridge.lean
Zeta23/GammaFacts/Mu.lean
```

These already provide exact physical arch normalization and a summable digamma-series representation. They may supply a cleaner complex continuation than differentiating the production real interval integrals directly.

Classification: **RESURRECTED LEAD**. The old bridge was not built for A4R, but #140 makes it newly relevant.

## Downstream regular first-bad target

Once finite-cell regularization is proved, compose with the existing first-bad and Schur machinery.

At the reselected state:

```text
A >= 0                         PROVED from first-bad minimality
A injective                    target from A4R
A positive definite           DERIVED in finite Hermitian dimension
unique x0 with A x0 = b        PROVED scaffold once regularity is supplied
u0 = c - x0
```

The intended packaged countercertificate is:

```text
Ecanonical(u0) = Re S0 < 0.
```

Existing #136/#137 machinery already supplies most of the energy/Schur bridge. A dedicated wrapper should be theoremized after A4R closes.

## Decisive arithmetic obstruction remains unchanged

Regularity is not positivity.

After resonance is removed, the hard arithmetic target is still:

```text
Ecanonical(c-x0) >= 0
```

for the exact forced regular first-bad trial `A x0=b`, equivalently in inverse shorthand:

```text
<b,A^-1 b> <= q_c.
```

Under predecessor positivity this is essentially the missing one-step Schur-complement positivity at the selected state. It must be proved by independent canonical arithmetic structure, not by assuming successor PSD under another name.

## Discovery guidance for the final sign

Use the exact #136 source-energy decomposition on the minimizing trial:

```text
pole
- reduced arch diagonal
- reduced arch off-diagonal
- scalar correction
- finite von-Mangoldt prime source sum.
```

The post-#138 diagnostics showed extreme cancellation and prime-weight sensitivity. Therefore:

- simplify using `A x0=b` before estimating;
- prefer combined-channel identities over termwise absolute bounds;
- interval-certify any low-dimensional conjectured sign before formal investment;
- reject atomwise determinant positivity/SOS unless a changed premise is proved.

## Falsification checks

A4R should be narrowed or abandoned if any of these fail:

1. the full frozen projected predecessor cannot be written with the theorem-backed scalar log term plus a suitable analytic remainder;
2. the archimedean remainder has hidden monodromy cancelling the scalar shift;
3. one parity/size block has a structural determinant identically zero on a cutoff cell;
4. fixed-witness canonical energy is not continuous on a frozen cutoff cell;
5. the determinant argument controls a different compression than `intrinsicPredecessorBlock`;
6. finite simultaneous avoidance cannot be composed with the preserved negative witness;
7. the reselected first-bad index can escape the regularized finite horizon despite the preserved negative witness at size `N`;
8. the final Schur sign candidate also holds for nearby modified source weights in a way incompatible with the known sensitivity experiments.

A failure of A4R narrows this route; it does not refute RH.

## Evidence labels after #140

**PROVED**

- theorem authority through PR #140;
- eventual negative canonical witness at every sufficiently large aperture under an off-line zero;
- eventual AnyParityBad and fresh global-first-bad selection;
- determinant/injectivity regularity equivalence;
- unique preimage on a regular predecessor;
- frozen prime matrix equality on a fixed cutoff cell;
- exact threshold atom vanishing;
- exact real-axis `-log L` scalar extraction.

**DERIVED**

- first-bad PSD + injective Hermitian predecessor -> positive definite predecessor;
- finite-cell regularization only needs finitely many sizes after a finite negative witness is obtained;
- an all-size Baire theorem is unnecessary for the preferred composition.

**LEAD / HYPOTHESIS**

- frozen-cell holomorphic/log-cover predecessor representation;
- determinant nonidentity by monodromy/eigenvalue counting;
- dense finite regularization;
- digamma bridge as the analytic continuation route;
- exact regular Schur-energy nonnegativity.

**EXPERIMENTAL SIGNAL**

- previously recorded high-cancellation canonical samples;
- prime-weight sensitivity;
- source-atom determinant leading-sign diagnostics.

**OPEN**

- dense regular-aperture theorem;
- regular first-bad countercertificate wrapper;
- regular canonical Schur-energy sign;
- finite negative-root exclusion;
- terminal Mathlib RiemannHypothesis bridge;
- RH.

## Highest-leverage next move

Build A4R1 around **one frozen cutoff cell**:

```text
fixed-cell continuity
+ actual predecessor analytic representation
+ determinant nonidentity
+ finite simultaneous avoidance
+ #140 aperture freedom
+ fresh first-bad reselection.
```

Do not build countable all-size Baire infrastructure unless this finite-cell route fails for a specific theoremized reason.

**RH remains OPEN.**
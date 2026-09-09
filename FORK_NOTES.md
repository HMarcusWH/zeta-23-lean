# Fork notes — current RHRC state

> **RH remains OPEN.**

## Authority snapshot

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

PR #140 is theorem-bearing and advances theorem authority beyond #137. It does not prove regular-aperture density, the final Schur sign, negative-root exclusion, or RH.

## Recent theorem packages

```text
#129 source-explicit cubic defect + exact cross-parity secular transfer
#131 exact canonical source-moment decomposition
#134 denominator-free whole-kernel source transport + direct zero-shift transfer
#136 absolute canonical source energy + scalar-sensitive production decomposition
#137 exact source pairing + one-step determinant + global sign-failure endpoint
#140 eventual aperture freedom + predecessor-regularity/frozen-cutoff scaffold
```

## What #140 adds

**PROVED:** a hypothetical off-line zero forces a finite boundary-flat canonical negative witness at every sufficiently large aperture. The finite size/vector may depend on the aperture.

**PROVED:** every sufficiently large aperture is `AnyParityBad` at some finite size and admits a freshly selected least global-first-bad size.

**PROVED:** determinant nonvanishing of the actual `intrinsicPredecessorBlock` is equivalent to injectivity and gives a unique preimage of every target, including the cubic shell coupling.

**PROVED:** frozen prime-cutoff equality, exact vanishing of an entering source atom at `L=log q`, and the real-axis scalar extraction `-2*wCorrection(L)=-log(L)+remainder(L)` for `L>0`.

## Current frontier after the #140 post-green pass

```text
A4b1 absolute canonical source energy                            PROVED / #136
A4b2a one-step determinant/sufficiency reduction                 PROVED / #137
A4R0  aperture freedom + regularity scaffold                     PROVED / #140
A4R1  fixed-cell finite regular-aperture selection               OPEN / NOW
A4b2r regular minimizing-trial Schur-energy sign                 OPEN / AFTER A4R1
A4b2b universal shell/determinant domination                     OPEN / BROAD FALLBACK
global first-bad exclusion                                       OPEN
terminal Mathlib RH wrapper                                      OPEN
RH                                                               OPEN
```

## Why the A4R plan simplified

The old plan moved one pre-existing finite witness and worried about simultaneous regularity before knowing its final finite horizon.

#140 changes the quantifiers:

```text
off-line zero -> badness at every sufficiently large aperture.
```

So choose one convenient frozen cutoff cell first, then obtain a finite witness inside it.

For large `Q`, work inside

```text
log Q < L < log(Q+1).
```

Choose interior `L1`, invoke #140 and obtain `(N,u)` with strict negative canonical energy. After `N` is known, only the finitely many predecessor blocks with both parities and `k<=N` need to be regularized. Continuity preserves the same strict negative witness on a small neighborhood; dense regularity for each fixed block then gives a finite-intersection selection; finally reselect global first-bad.

Therefore an all-size countable Baire theorem and prime-threshold crossing are not primary obligations.

## Intended A4R1 theorem shape

```text
one frozen cutoff cell
  -> fixed-witness continuity
  -> actual predecessor analytic/log-cover representation
  -> determinant nonidentity for each fixed parity/size
  -> dense fixed-block regularity
  -> finite simultaneous avoidance through a chosen M
  -> preserve finite negative witness
  -> fresh global first-bad reselection.
```

The #140 scalar `-log(L)` coefficient is already theorem-backed. The hard analytic obligation is the full production predecessor remainder, especially the archimedean channel. Existing dictionary/digamma files are now a resurrected route for that continuation.

## After A4R1

At the reselected first-bad state, predecessor minimality gives `A>=0`; regularity gives injectivity and the #140 scaffold gives a unique `x0` with

```text
A x0 = b.
```

Set

```text
u0 = c - x0.
```

The intended packaged forced countercertificate is

```text
Ecanonical(u0) = Re S0 < 0.
```

The decisive arithmetic target remains

```text
Ecanonical(c-x0) >= 0
```

or equivalently `<b,A^-1b> <= q_c` once inverse shorthand is legal. It must come from exact canonical prime/arch/scalar structure rather than a renamed successor-positivity assumption.

## Research constraints preserved

- universal `q_c/Delta` nonnegativity is DERIVED equivalent to successor positivity under the present block hypotheses;
- `Delta(P_kerA b)=-||P_kerA b||^4` is a DERIVED resonant witness;
- the correction-vector proportionality signal removes one hoped-for independence route;
- atomwise determinant positivity is disfavored by the recorded negative leading coefficient;
- sampled canonical Schur energies are extremely cancellation-sensitive;
- modified prime-weight experiments show exact arithmetic coefficients matter.

## Firewalls

- RH remains OPEN.
- theorem authority is through #140 only.
- aperture freedom is PROVED; dense regular-aperture selection is OPEN.
- regularity is not successor positivity.
- the regular scalar sign theorem is OPEN.
- no all-size Baire infrastructure is required unless the finite-cell route fails for a theoremized reason.
- no zero-shift inverse is required in Lean before regularity; use the unique-preimage interface.
- no termwise source-atom positivity shortcut.
- no factorwise division by unproved transfer quantities.
- D remains algebraic, not unitary/isometric.
- machine claim promotion remains separate.

Newest research detail: `research/RHRC/RESEARCH_LEADS_POST_140_APERTURE_FREEDOM_DELTA.md`.

**RH remains OPEN.**
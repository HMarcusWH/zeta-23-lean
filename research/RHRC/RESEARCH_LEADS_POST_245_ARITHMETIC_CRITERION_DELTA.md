# Post-#245 research delta — the route's last node is RH, stated arithmetically

## What became formally true

Merged PR #245 proves that both terminal certificate gates are equivalent to
Mathlib's exact `RiemannHypothesis`.

Validated object:
- PR: #245
- head: `766579346ec86b25d63fb61f8e0b46752a028f6c`
- merge: `ad0347ef07e2c7717f88bd9d8bf7555be75ad88e`
- tree: `0466006ec23b3f24f6ea113b303014ae42a680dd`
- repository inventory at the merge tree: 1,081 blobs; `Zeta23/CCM` 205 files;
  `Zeta23/ExceptionalZero` 72 files
- attached workflows: 11/11 successful (13/13 check runs)

Exact theorems:

```lean
Zeta23.ExceptionalZero.noRegularFirstBadCertificates_iff_riemannHypothesis :
  NoRegularFirstBadCertificates ↔ RiemannHypothesis

Zeta23.ExceptionalZero.noArbitrarilyLargeWholeCellRetainedFamily_iff_riemannHypothesis :
  NoArbitrarilyLargeWholeCellRetainedFamily ↔ RiemannHypothesis
```

The reverse direction is critical-line Weil positivity transported through the
exact boundary-flat finite identity: under RH no retained negative-energy
certificate exists at any aperture.

The post-#245 arithmetic-criterion PR (candidate, not yet theorem authority)
adds two modules.

`Zeta23/CCM/CanonicalPrimeRemainder.lean` (unconditional; imports nothing from
the terminal layer) proves:

```text
canonicalPrimeCumulativeWeight L t = ∑_{n ≤ e^t} Λ(n)/√n          (t ≤ L)
canonicalPoleCumulativeWeight t    = 2√(e^t) - 2 e^{-t/2}
canonicalPolePrimeDiscrepancy L t  = -2 e^{-t/2} - R(e^t)            (t ≤ L)
R(x)                               := ∑_{n ≤ x} Λ(n)/√n - 2√x

canonicalSourceChannelEnergy L K x
  = -canonicalPrimeRemainderEnergy L K x - canonicalPrimeFreeBudget L K x
```

where `canonicalPrimeRemainderEnergy` is the energy of `R(e^t)` against the
exact source-atom derivative and `canonicalPrimeFreeBudget` collects the pole
tail and the reduced archimedean diagonal, off-diagonal and scalar channels.
The weighted sum is literally the quantity in `Zeta23.ChebyshevMertens.cheb1b`.

`Zeta23/ExceptionalZero/CanonicalArithmeticCriterion.lean` proves, with no new
hypothesis:

```text
CanonicalFiniteWeilPositivity                   ↔ RiemannHypothesis
CanonicalRieszSixPositivity                     ↔ RiemannHypothesis
GeneratedRetainedRieszSixEventuallyNonnegative  ↔ RiemannHypothesis
CanonicalPrimeRemainderDominance                ↔ RiemannHypothesis
GeneratedRetainedPrimeRemainderDominance        ↔ RiemannHypothesis
```

and exhibits the first failed inequality forced by an off-line zero:

```text
exists_arbitrarilyLarge_primeRemainderDominance_failure_of_offLine_zero :
  off-line zero -> ∀ A, ∃ generated whole-cell retained c with L > A and
    -canonicalPrimeRemainderEnergy L K trial < canonicalPrimeFreeBudget L K trial
```

RH remains OPEN.

## Workflow harvest

All 11 workflows attached to the #245 head completed successfully.

Formal/control:
- CCM build — SUCCESS
- ExceptionalZero build — SUCCESS
- forbidden-placeholder gate — SUCCESS
- claim lint / registry lint / promoted-binding lint — SUCCESS
- Control-v2 suite — SUCCESS
- R003 normalization audit — SUCCESS
- Permansson formal verification — SUCCESS (unrelated formal regression)

Research/regression:
- post-190, post-192, post-194, post-196, post-198 — frozen replays preserved;
- post-200 — `DISCREPANCY_REPRESENTATION_DEPENDENCY_UNRESOLVED`: 49/49
  completed leaves unresolved, zero positive paired-source leaves, no unique
  lock;
- post-202 — `COMPOSITE_PARITY_GAP_PATTERN_FALSIFIED`; the kill switch fired
  before the full-cover computation, as designed;
- post-214 — full-space dual independence/sign-indefiniteness preserved;
- post-222 — `NO_FROZEN_CELL_MINIMAL_BIREGULAR_STATE_CERTIFIED`.

Green on post-200 and post-202 means the falsification machinery worked. No
research replay promotes a theorem.

## What changed

Before #245 the route could still be described as "one more gate strictly
below RH". After #245 it cannot. The two gates are RH-equivalent, hence
equivalent to each other; the earlier statement that the generated-family gate
is strictly weaker than `NoRegularFirstBadCertificates` is superseded.

Every candidate "last lemma" proposed after #245 has now been checked against
the same firewall, as compiled equivalences:

| candidate primitive target | status |
| --- | --- |
| eventual Riesz-six nonnegativity on the generated retained trial | RH-equivalent |
| Riesz-six nonnegativity on every boundary-flat carrier | RH-equivalent |
| canonical finite Weil positivity | RH-equivalent |
| explicit prime-remainder dominance | RH-equivalent |
| same, only eventually along the generated family | RH-equivalent |

The Riesz-six case is not merely "close to" RH-strength: on every boundary-flat
carrier the complete order-six Riesz channel equals the canonical source energy
(`canonicalSourceChannelEnergy_eq_rieszSix_of_boundaryFlat`), so the proposed
target is literally the #245 gate.

Consequently: **no sub-RH gate remains on this route.** The route's last node
is RH itself, now written as one explicit weighted von Mangoldt inequality.

## Upstream implications

The only prime-dependent quantity in the complete canonical energy is the
classical remainder `R(x) = ∑_{n ≤ x} Λ(n)/√n - 2√x`. The inequality is linear
in `R`.

What the repository proves unconditionally about `R` is magnitude:
- `Zeta23.Cheb.sum_vonMangoldt_div_sqrt_le_three` gives `R(x) ≤ √x` for large
  `x`; trivially `R(x) ≥ -2√x`.
- `Zeta23/FromPNTPlus/MediumPNT.lean` states `ψ(x) - x = O(x exp(-c (log x)^{1/10}))`.
  No module imports it and CI never builds it, so it is not part of the
  verified dependency graph today.

Classical context (literature, not formalized here): under RH, von Koch's
bound `ψ(x) - x = O(√x log² x)` gives `R(x) = O(log³ x)`; conversely any bound
`R(x) = O(x^θ)` with `θ < 1/2` would give `ψ(x) - x = O(x^{1/2+θ})` and hence a
zero-free half-plane `Re s > 1/2 + θ`, which is open for every `θ < 1/2`.

## Downstream implications

A proof of `CanonicalPrimeRemainderDominance` from unconditional inputs would be
a proof of RH: the implication to Mathlib's `RiemannHypothesis` already
compiles, with no new analytic glue. There is no engineering layer left
between the arithmetic inequality and the terminal statement.

Conversely, no further terminal wrapper, final gate, or renamed positivity
property can reduce the problem. Future PRs on this route should not add one.

## Resurrected routes

None is resurrected by this delta. The contact route remains fallback only.
Any route that terminates in exclusion of retained certificates, in canonical
finite Weil positivity, or in a Riesz-channel sign on boundary-flat carriers is
RH-equivalent by the equivalences above. A route is only genuinely new if it
brings RH-strength arithmetic input from outside the finite canonical energy.

## New RH-relevant clues

The prime-free budget is completely explicit and prime-free: the pole tail
`2 e^{-t/2}` and the reduced archimedean Gamma channels. The entire arithmetic
content of the canonical energy is one linear functional of the classical
remainder `R` on `[1, e^L]`, tested against the smooth source-atom derivative.
This is the finite canonical form of Weil's criterion, not a new criterion.

## Falsification checks

- Any claimed proof whose prime-side input is an envelope `|R(x)| ≤ F(x)` with
  `F` growing faster than every power of `log x` should be treated as wrong
  until the budget growth is checked. Heuristic (DERIVED, not formalized): the
  inequality is linear in `R`, so perturbing `R` inside such an envelope with
  the sign opposite to the source-atom weight violates it once the envelope
  exceeds the prime-free budget, provided that budget grows subexponentially in
  `L` at fixed normalized carrier.
- Any proof that does not use the Euler product beyond Chebyshev-type magnitude
  is suspect for the same reason.
- Any proof that compiles but depends on the terminal layer, `sorryAx`, or a
  project axiom is rejected by the new firewall and axiom-audit CI steps.

## Highest-leverage next moves

1. Stop adding terminal gates on this route; they are all RH.
2. If the route continues, the honest target is RH-strength information about
   `R(x)` itself, i.e. new mathematics about the zeros of ζ, not about the
   finite canonical carrier.
3. Optional unconditional hygiene: bring `MediumPNT.lean` into the verified
   build graph and theoremize `R(x) = o(√x)`. This quantifies the gap; it
   cannot close it.

## Standing questions

Does any retained-state structure (whole-cell badness, bi-regularity, the
cubic zero-shift trial) restrict the source-atom weight enough to change the
linear-in-`R` analysis? By #245 the answer cannot yield a sub-RH closure, but it
could identify which scales of `R` the canonical carrier actually probes.

How fast does `canonicalPrimeFreeBudget L K x` grow in `L` at fixed normalized
carrier? This decides the quantitative form of the falsification heuristic.

**RH remains OPEN.**

# Post-#245 dead-route delta

## What became formally true

PR #245 proves both terminal certificate gates equivalent to Mathlib's
`RiemannHypothesis`. The post-#245 arithmetic-criterion PR (candidate) proves
the same for every candidate "last lemma" proposed afterwards, and writes the
canonical energy as minus a classical prime-remainder energy minus an explicit
prime-free budget.

## Workflow harvest

11/11 workflows attached to the #245 head completed successfully. post-200 and
post-202 are green because their falsification machinery worked:
`DISCREPANCY_REPRESENTATION_DEPENDENCY_UNRESOLVED` (0/49 positive paired-source
leaves) and `COMPOSITE_PARITY_GAP_PATTERN_FALSIFIED`.

## What changed

### Closed as RH-equivalent — do not spend theorem PRs on these as "last lemmas"

- `NoRegularFirstBadCertificates` — RH-equivalent (#245);
- `NoArbitrarilyLargeWholeCellRetainedFamily` / eventual aperture bound —
  RH-equivalent (#245);
- eventual Riesz-six nonnegativity on the generated retained trial —
  RH-equivalent (candidate);
- Riesz-six or canonical energy nonnegativity on boundary-flat carriers —
  RH-equivalent (candidate);
- prime-remainder dominance, universal or generated-family-eventual —
  RH-equivalent (candidate).

### Still dead / invalid

- a sign for the pole-prime discrepancy obtained by source decomposition
  (post-200: 49/49 leaves unresolved);
- fitting a theorem to the Q14 composite sign pattern (post-202 falsified it);
- `D > 0`, `Gamma > 0`, `Rsharp ≤ q²` or `Alpha ≥ 1` as a closing lemma: each is
  a classification step, not a contradiction;
- swapping `∀ L in cell, ∃ K` for `∃ K, ∀ L in cell` in whole-cell badness;
- magnitude-only prime inputs (Chebyshev/Mertens/PNT-envelope strength) as a
  proof of dominance (heuristic, see the research delta);
- numerical/frozen Q14 evidence as arbitrary-`Q` theorem authority.

## Upstream implications

The canonical CCM prime staircase is the classical weighted Chebyshev sum; no
hidden CCM-specific arithmetic remains unexploited in `PrimeUpper.lean`
(`prime_side_libraries_available : True` is a placeholder marker only).

## Downstream implications

No terminal wrapper can make progress; the Mathlib seam and both gate
compositions already compile.

## Resurrected routes

None.

## New RH-relevant clues

The remaining content is exactly the size and oscillation of
`R(x) = ∑_{n ≤ x} Λ(n)/√n - 2√x`, i.e. of the zeros of ζ.

## Falsification checks

The arithmetic firewall lint rejects any `Zeta23.CCM` module that reaches a
terminal module or mentions `RiemannHypothesis`; the axiom audit rejects
`sorryAx` and project axioms in the new modules.

## Highest-leverage next moves

Treat the route as fully reduced unless genuinely new RH-strength input about
`R` is available.

## Standing questions

Is there any retained-state constraint that is not a consequence of canonical
finite Weil positivity and could therefore serve as independent input? By #245
such a constraint could at most be RH-equivalent at the terminal.

**RH remains OPEN.**

# HMWH Zeta23 fork — research boundary and provenance

This file defines the fork-level boundary. It supersedes the earlier description of the fork as only an "exceptional-zero detection" extension.

## Preserved upstream baseline

The fork baseline is pinned in `UPSTREAM_BASELINE.json`:

```text
upstream: anthropics/zeta-23-lean
baseline fork commit: cec57f919ccf34e5fa5372b4ba332f7c848bbb6e
```

The inherited Zeta23 paper formalization remains a preserved foundation. The fork does not rewrite its historical provenance.

The old root README and audit are retained as `UPSTREAM_README.md` and `UPSTREAM_AUDIT.md`.

## Fork theorem-bearing mathematics

Fork-owned formal mathematics now extends well beyond `Zeta23/ExceptionalZero/`.

Major theorem-bearing areas include:

- `Zeta23/ExceptionalZero/` — exceptional-zero amplification, two-translate detectors, multi-probe separation and related exact mathematics;
- `Zeta23/CCM/` — finite CCM matrix calculus, finite Guinand--Weil dictionary, explicit-formula extension, zero-side bridge, localized finite Fourier spaces, source normalization and displacement structure;
- supporting fork additions used by those routes.

All promoted fork mathematics must remain sorry-free and may not introduce project-specific axioms.

Open obligations belong in the claim/route registries and route documents, not as Lean axioms.

## Research control plane

Everything under `research/RHRC/` is one of:

- discovery tooling;
- source/provenance mapping;
- falsification and countermodels;
- route governance;
- numerical diagnostics;
- evidence receipts;
- machine-readable claim and route state.

These materials may guide proof search but are not theorem authority.

## Canonical CCM naming rule

The canonical direct-source finite object is

```text
canonicalSourceMatrix
  = cutoffFreeMatrix
  = sourceEq44Matrix
  = dictionaryMatrix.
```

The historical literal printed normalization is

```text
legacyPrintedMatrix = finiteMatrix.
```

The two differ by a scalar identity shift. The legacy object must never be silently relabelled as the ambient source restriction `QW_lambda|E_N`.

Any claim about absolute spectrum, PSD, inertia, lower bounds, trace or determinant must state which normalization it uses.

## Route state

The fork currently tracks:

- **R001** exceptional-zero amplification;
- **R002** multi-probe / negative-index observables;
- **R003** CCM / finite Weil bridge;
- **R004** finite displacement / prolate-structure investigation.

The present critical path starts from the now-PROVED W0 function-level obstruction: every hypothetical off-line zero yields one compact C² pole-neutral test with negative genuine Weil self-value. The immediate next package is W1, which must recenter that test into strict support inside one finite positive aperture while preserving pole neutrality and W negativity. After W1, the program splits into the internal additive lane (W2-B/W2-C/F0-B/G1-A) and the source-faithful lane (G1-B1B/G1-final/G23), both targeting the same F1 canonical finite obstruction. The preferred K0-K3 finite-wall program after F1 is a planned research route, not yet a theorem-backed terminal reduction; K1 must first establish the positive-anchor/continuous-aperture first-crossing mechanism for the same finite sector. R001 and R002 remain mathematically useful alternates. R004 is retained as structural support and a dormant composition source.

## FFBBP / OoL boundary

FFBBP and OoL-MVS contribute research-process and discovery/governance semantics only.

The currently qualified FFBBP lineage is RUN42C with the inductive firewall; RUN42B is historical/quarantined development lineage.

OoL-MVS v2.7.6 remains a route-governance reference only. Origin-of-life claims are not RH premises.

Neither FFBBP nor OoL-MVS can promote a mathematical theorem.

## Permanent rules

1. **Lean/compiler/CI is theorem authority.**
2. **Research machinery is not a theorem dependency.**
3. **RH stays OPEN until the exact final RH theorem is proved and claim-validated; a planned first-crossing route is not a terminal reduction until its intermediate implications are theorem-backed.**
4. **A finite formula identity is not automatically an ambient Hilbert/form restriction theorem.**
5. **A function-level source representative is not automatically a bundled L2/form-domain object.**
6. **Normalization, parameterization, carrier space, measure, functional, and restriction map are separate interfaces and must be closed separately.**
7. **Scalar-shift-invariant evidence cannot be upgraded into scalar-shift-sensitive spectral claims.**
8. **Synthetic worlds and numerical experiments are discovery/falsification evidence only.**
9. **Conditional, numerical, heuristic and synthetic ancestry cannot be laundered into unconditional theorem status.**
10. **Dead routes may be revisited only when the blocking premise has changed and that change is stated explicitly.**
11. **Green triggers a post-green research pass; it does not terminate investigation.**
12. **The fork may search aggressively and must promote conservatively.**

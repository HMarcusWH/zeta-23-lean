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

Merged main `5134e81c0ce3fa37ef593eb96125d8e4d5aa09b8` (through PR #82) is theorem-locked through W1: every hypothetical off-line zero yields one compact C² pole-neutral negative Weil test, then a common translation places its closed support in an explicit strict margin `(r,3r)` inside aperture `L=4r` while preserving both pole zeros and the exact negative Weil self-value.

The post-W1 investigation changed the next internal priority. The first spike is now concrete-zeta zero-side evenization: use Schwarz conjugation plus the existing `rho -> 1-conj(rho)` functional-equation symmetry to test a theorem-authoritative `rho -> 1-rho` carrier equivalence, spectral sign reversal, Fourier reflection and summability-safe `EF_lit` reindex. If this closes, W2-B/C may compress to a direct diagonal W/additive theorem. This is a **LEAD**, not formal truth.

The previous pole-neutrality + mu/gamma + weighted-integrability route remains fallback. On the source side, `S-GEOM` owns the exact `L <-> lambda` bridge and `S-IFACE` owns the d*u/L²/kappa/q/PsiSharp/QW interface before G1-B1B. Neither supplies strict source negativity. Feeding G23 additionally requires `S-NEG` (an independent fixed-aperture negative-QW theorem) or an exact theorem carrying the negative W/localized-additive value into QW. Whichever route reaches F1 with the smaller clean theorem surface becomes primary; independent closure by more than one route remains valuable.

The preferred K0-K3 finite-wall program after F1 remains planned, not theorem-backed; K1 must still establish the same-sector positive-anchor/first-crossing mechanism. R001 and R002 remain mathematically useful alternates. R004 is retained as structural support and a dormant composition source.

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

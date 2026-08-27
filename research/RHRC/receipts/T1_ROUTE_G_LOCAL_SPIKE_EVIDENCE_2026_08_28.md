# T-1 Route G local spike evidence — 2026-08-28

Status: **LOCAL-COMPILED / REJECTED AS PRODUCTION / SOURCE NOT PRESENT IN GITHUB**

## Pinned repository state

- Repository: `HMarcusWH/zeta-23-lean`
- Base commit checked by the project handover: `f561cb34df1d95a2898c92720085e991a5cbe75b`
- Base tree: `6cd7f27879c76386953f8e8e2cbea80c4b076405`
- Latest merged PR at freeze: #52

## Evidence preserved

The project handover records a local compiler spike named
`DictionaryTentGuinandWeilSpike.lean` exploring the direct Route-G strategy:
extend/adapt the inherited Guinand--Weil explicit-formula chassis so the
canonical nonsmooth tent can be admitted directly.

The spike reportedly compiled locally, but the exact source file was not
committed, pushed, attached to a GitHub PR, or otherwise recoverable from the
repository at the time of this archival pass.

Searches performed against the repository on 2026-08-28 found no:

- file named `DictionaryTentGuinandWeilSpike.lean`;
- code-search hit for `DictionaryTentGuinandWeilSpike`;
- branch containing `route-g`, `guinand`, or the spike name;
- commit-search hit carrying the spike;
- PR/issue text carrying the spike source.

## Claim firewall

This receipt **does not reconstruct the missing source** and does not upgrade
the local spike into a theorem-bearing Git artifact.

It preserves only the project-state fact recorded by the handover:

- Route G was locally compiler-feasible enough to demonstrate that a direct
  tent admission path was not syntactically impossible;
- Route G was rejected as the production architecture because it would spread
  the nonsmooth exception through a broad `ContDiff ℝ 2`-dependent WeilEF
  graph;
- the exact original local source is unavailable on GitHub and therefore cannot
  be independently recompiled or audited from this branch.

## Production consequence

Do not merge this archival branch into `main`.

Production work proceeds through Route M: a local mollifier/limit adapter around
the canonical `dictionaryTent`, leaving the central WeilEF API unchanged
unless the Route-M architecture fails its compiler gates.

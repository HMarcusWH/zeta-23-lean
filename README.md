# Zeta23 / RHRC — Lean-backed Riemann Hypothesis research fork

> **Claim firewall: the Riemann Hypothesis is OPEN in this repository.**
>
> Green supporting theorems, finite matrix identities, numerical experiments, source-formula agreement, displacement structure, or route closure below the terminal theorem do not constitute a proof of RH.

This repository began as a fork of Anthropic's Lean 4 formalization accompanying **"More than two thirds of the zeros of the Riemann zeta function are simple and on the critical line"** (arXiv:2608.13637). The inherited Zeta23 formalization remains the baseline analytic and linear-algebra library.

The fork is now an active research repository pursuing exact, falsifiable routes toward the Riemann Hypothesis. The additional work includes exceptional-zero detectors, two-translate theorems, finite Guinand--Weil dictionaries, explicit-formula extensions, exact finite zero-side matrices, Connes--Consani--Moscovici (CCM) finite source normalization, localized Fourier spaces, and a developing fixed-aperture Weil-form / variational route.

The original upstream README is preserved at [UPSTREAM_README.md](UPSTREAM_README.md). The original upstream audit is preserved at [UPSTREAM_AUDIT.md](UPSTREAM_AUDIT.md). [formalization.yaml](formalization.yaml) describes that preserved upstream formalization layer; it is not a complete metadata description of the later HMWH RH research extensions.

## Repository identity

There are two deliberately separated layers.

### 1. Preserved Zeta23 baseline

The inherited project proves the paper's headline zero-proportion theorems and supporting analytic infrastructure in Lean 4 / Mathlib. Its baseline is pinned in [UPSTREAM_BASELINE.json](UPSTREAM_BASELINE.json).

Important inherited assets include:

- Weil explicit-formula machinery;
- Riemann--von Mangoldt counting;
- gamma/Stirling estimates;
- prime-side estimates;
- linear algebra including inertia, Weyl bounds, and rank--trace tools;
- the original comparator-checked theorem surface.

### 2. HMWH RH research fork

The fork adds theorem-bearing Lean code under, among other places:

- `Zeta23/ExceptionalZero/`;
- `Zeta23/CCM/`;
- selected supporting linear-algebra and route-integration modules.

Research governance, discovery tooling, source maps, falsifiers, route registries, and evidence receipts live under `research/RHRC/`.

Two living research-control SSOTs are maintained there:

- [RESEARCH_LEADS.md](research/RHRC/RESEARCH_LEADS.md) — the complete accumulated lead inventory: active, testing, blocked, dormant, promoted, refuted and quarantined ideas, with formal status, evidence, blockers, composition opportunities and cheapest falsifiers;
- [CURRENT_RESEARCH_PLAN.md](research/RHRC/CURRENT_RESEARCH_PLAN.md) — the current execution order from the exact merged theorem state, including parallel lanes, decision gates, stop conditions and post-F1 work.

The distinction is deliberate: the lead ledger remembers the whole research option space; the current plan says what to build next. Neither overrides Lean/compiler/CI or the machine claim/route registries.

The rule is strict:

> Research tooling may suggest or falsify. Lean/compiler/CI determines theoremhood.

## Current RH route map

The live research program is organized as four principal routes.

### R001 — exceptional-zero amplification

The zero-side exposed-pole / filtered-growth chain is formally strong, but the remaining scalar arithmetic upper-bound target has itself been proved RH-equivalent. R001 is therefore not treated as an easier terminal route.

### R002 — multi-probe / negative-index route

Exact block-level off-critical separation has been proved. Generic windowed visibility and its arithmetic leg remain open; the latter is a band-limited Weil-positivity problem. PR #66 also proved that the generic smooth-taper R002 production object is **not** simply the canonical CCM finite object in another basis.


### R003 — CCM / finite Weil bridge

This remains the active finite-obstruction route. The merged theorem state now includes W2-A, W0, W1, W2-ZS, the direct diagonal W/localized-additive identity, and the strict-aperture negative localized-additive witness.

Merged state:

~~~text
main = 9e899ca322116e28a56a4412d48aef0052b86fbe
tree = ad636143768dcaa4dbeb23a0ea295d7b2d6b1c9b
merged through = PR #84
PR #83 theorem head = 556be6c2b42e912c58751988c580ab4e0091822d
PR #83 merge = 7b8e0cc9abbaeff97d88ec67ada40734619a8d07
PR #84 final validated head = 1a518c9ebd408fa559c5eff281eafe5ff3b2af48
RH = OPEN
~~~

The shared function-level obstruction is now theorem-locked all the way to the repository localized additive functional:

~~~text
off-line zero
  -> W0 compact C² pole-neutral h with Re W(h,h)<0
  -> W1 strict aperture:
       L=4r,
       tsupport h ⊂ (r,3r) ⊂ (0,L)
  -> W2-ZS / direct diagonal bridge:
       W(h,h)=localizedWeilAdditiveRHS(h,h)
  -> Re(localizedWeilAdditiveRHS(h,h))<0.
~~~

The generic bridge theorem is

~~~text
Zeta23.ExceptionalZero.zeta_W_self_eq_localizedWeilAdditiveRHS
~~~

and the strong F0-B input is

~~~text
Zeta23.ExceptionalZero.
exists_strictAperture_poleNeutral_negativeLocalizedWeilAdditiveRHS_of_offLine_zero.
~~~

PR #83 proves the concrete-zeta zero-side route by theoremizing `rho -> 1-rho` on the actual zero carrier with multiplicity, exact `gammaOf` sign reversal, Fourier reflection, and summability-safe zero-sum reindexing. It does not need the old analytic `mu`/gamma reflection or weighted gamma-integrability route.

Therefore the shortest internal route is now:

~~~text
negative localized-additive witness
  -> F0-B finite approximation / continuity             [OPEN]
  -> G1-A finite additive restriction                    [PROVED]
  -> F1 canonical finite negative obstruction           [OPEN].
~~~

F0-B has two live bounded candidates:

~~~text
F0-B1:
  boundary-flat globally C² finite Fourier approximants
  + W continuity

F0-B2:
  direct localized-additive continuity
  on the existing legal finite vectors.
~~~

No route is selected until the topology/continuity burden is theoremically inspected. Pointwise summability for each approximant is not a uniform family-level domination theorem.

The old analytic W2-B route remains OPEN / DORMANT as an independent cross-check; proving the diagonal endpoint via W2-ZS does not prove that historical route.

The source-faithful lane remains active in parallel:

~~~text
SOURCE INFRASTRUCTURE
  S-GEOM L <-> lambda
  S-IFACE d*u/L²/kappa/q/PsiSharp/QW
  -> G1-B1B -> G1-final

SOURCE NEGATIVITY ENTRY
  S-NEG independent fixed-aperture negative-QW theorem
  or exact W/localized/QW sign composition

COMMON
  negative ambient QW + finite restriction
  -> G23
  -> F1.
~~~

By OBS-015, the source interface theorems do not themselves transport the W1/#83 strict negative sign into QW.

The preferred K0-K3 finite-wall program after F1 remains planned research, not a theorem-backed terminal reduction.

### R004 — finite displacement / structural route

The exact centered-index displacement law and rank-at-most-two consequence are theorem-authoritative. The older fitted-tridiagonal small-commutator -> eigenvector-convergence story is not supported because the fitted generator's spectral gaps collapse on tested finite cases.

R004 remains useful as a structural tool, not a proof of RH.

## Canonical CCM object firewall

After the source audit and normalization repair, the theorem-authoritative direct-source finite object is

```text
canonicalSourceMatrix
  = cutoffFreeMatrix
  = sourceEq44Matrix
  = dictionaryMatrix
  = zeroSideMatrix            (under the proved positive-aperture bridge).
```

The historical literal printed-(4.11)/(4.14) object is

```text
legacyPrintedMatrix = finiteMatrix.
```

Lean proves the scalar-shift relation

```text
canonicalSourceMatrix
  = legacyPrintedMatrix
    + 2*legacyPrintedCorrection(L)*I.
```

This distinction is mathematically important.

Scalar identity shifts preserve:

- commutators and displacement laws;
- eigenvectors/eigenspaces;
- eigenvalue gaps and ordering.

They do **not** preserve:

- absolute eigenvalues;
- positivity / PSD;
- inertia;
- lower bounds;
- trace or determinant.

Any downstream spectral-sign argument must therefore identify the canonical matrix explicitly.


## Current critical path

The stable work-package names, not historical PR numbers, define the mathematics.

Validated shared infrastructure:

~~~text
canonical countable detector bank                         CLOSED
finite dictionary / zero-side bridge                      CLOSED
cutoff-free/canonical finite source matrix                CLOSED
G0 localized basis + finite space                         CLOSED
G1-A additive finite restriction                          CLOSED
direct source normalization/firewall                      CLOSED
G1-B1A finite kappa/source-sector bridge                  CLOSED
W2-A genuine W/literatureRHS bridge + summability         CLOSED
W0 off-line zero -> compact C² pole-neutral negative h    CLOSED
W1 strict finite-aperture recentering with margin         CLOSED
W2-ZS zero-side evenization                               CLOSED
direct diagonal W2-C endpoint                             CLOSED
negative localized-additive strict-aperture witness       CLOSED
~~~

Current execution priority:

~~~text
INTERNAL — NOW
  F0-B finite approximation / strict-negativity transfer  OPEN
    F0-B1 boundary-flat global C² approximants
      + W continuity
    F0-B2 direct localized-additive continuity
    WCONT topology / family-level domination gate

INTERNAL FALLBACK / CROSS-CHECK
  I0 pole-neutrality transfer                              OPEN
  I1 mu/gamma reflection evenness                          OPEN
  I2 weighted gamma-channel integrability                  OPEN
  old analytic W2-B / analytic W2-C proof route            OPEN

SOURCE — PARALLEL
  S-GEOM exact L <-> lambda bridge                         OPEN
  S-IFACE G1-B1B premise/normalization lock                OPEN
  G1-final actual source restriction                       OPEN
  S-NEG negative-QW entry or exact W/localized/QW bridge   OPEN
  G23 negative finite transfer                             OPEN
~~~

Primary internal continuation:

~~~text
F0-B -> G1-A [CLOSED] -> F1.
~~~

Source continuation:

~~~text
G1-B1B -> G1-final
+
theorem-backed negative-QW entry
-> G23 -> F1.
~~~

Shared target:

~~~text
F1:
off-line zero
  -> exists L>0, N, u,
     Re(quadraticForm(canonicalSourceMatrix L N) u) < 0.
~~~

F1 is not RH. RH remains OPEN.

## Evidence and authority order

When documents disagree, use this order:

1. live GitHub head, Lean compiler, and CI;
2. `research/RHRC/CLAIM_REGISTRY.json` and `research/RHRC/routes/ROUTE_REGISTRY.json`;
3. the active route README, especially `research/RHRC/routes/R003_ccm_bridge/README.md`;
4. the living research-control SSOTs — `RESEARCH_LEADS.md` for option/status memory and `CURRENT_RESEARCH_PLAN.md` for execution order;
5. the current external build-plan / handover SSOT;
6. PR-specific settlement documents;
7. older route plans, numerical receipts, and historical audits.

See [research/RHRC/DOCUMENTATION_AUTHORITY.md](research/RHRC/DOCUMENTATION_AUTHORITY.md).

## Post-green rule

Green is not the end of a research PR.

After every meaningful green result the project:

- verifies the exact checked head and theorem declarations;
- reads the successful proof and its assumptions;
- compares it with earlier attempts and route history;
- searches upstream and downstream implications;
- revisits previously failed routes whose prerequisites changed;
- tries to falsify new RH-relevant clues;
- updates route state without upgrading claims beyond what Lean proved;
- updates the living lead ledger and current plan whenever a lead is promoted, killed, resurrected, blocked, or reprioritized.

RH remains OPEN unless the exact terminal RH theorem passes the full proof and claim-validation gates.

## Repository layout

```text
comparator/                      preserved upstream trusted-statement/comparator layer
Zeta23/                          Lean mathematics
Zeta23/ExceptionalZero/          R001/R002 theorem-bearing fork work
Zeta23/CCM/                      R003/R004 finite CCM/Weil formalization
research/RHRC/                   route control plane, source maps, audits, falsifiers, receipts
research/RHRC/RESEARCH_LEADS.md   living complete research-lead inventory
research/RHRC/CURRENT_RESEARCH_PLAN.md living execution plan from merged theorem state
research/RHRC/routes/R001_*      exceptional-zero route
research/RHRC/routes/R002_*      multi-probe route
research/RHRC/routes/R003_*      CCM / finite Weil bridge
research/RHRC/routes/R004_*      displacement / prolate-structure diagnostics
UPSTREAM_BASELINE.json           immutable fork baseline
UPSTREAM_README.md               preserved pre-fork-facing README snapshot
UPSTREAM_AUDIT.md                preserved upstream audit snapshot
```

## Building and checking

The pinned Lean/Mathlib toolchain remains controlled by `lean-toolchain` and `lake-manifest.json`.

Useful checks include:

```bash
lake exe cache get
lake build
lake build Zeta23.ExceptionalZero
lake build Zeta23.CCM

python research/RHRC/tools/run_suite.py
python research/RHRC/routes/R003_ccm_bridge/check_source_normalization_firewall.py
python research/RHRC/routes/R004_prolate_v2/check_normalization_shift_invariants.py
```

The comparator instructions for the preserved upstream theorem surface remain in [comparator/README.md](comparator/README.md).

## Provenance

The fork preserves the inherited Apache-2.0 project and its upstream notices. See [NOTICE](NOTICE), [LICENSE](LICENSE), [UPSTREAM_BASELINE.json](UPSTREAM_BASELINE.json), and [FORK_NOTES.md](FORK_NOTES.md).

External numerical/source implementations under `research/RHRC/external/` are reference and falsification oracles only. They are forbidden from becoming Lean theorem dependencies.

## Current terminal status

```text
RIEMANN HYPOTHESIS: OPEN
```

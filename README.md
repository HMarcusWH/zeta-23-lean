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

This remains the active finite-obstruction route. W2-A, W0 and W1 are theorem-authoritative on merged main through PR #81.

Merged state:

~~~text
main = 1a6a286cc4aae76ef6335b85b1022ec3998614df
tree = 1d49b9dc4fbee4054d18ce5059b40c2d7ccbc3cf
merged through = PR #81
PR #81 final validated head = 191e34ece05739122f362d097f9e4393cd5b9ce3
RH = OPEN
~~~

The shared function-level front end is closed:

~~~text
off-line zero
  -> W0 compact C² pole-neutral h with Re W(h,h)<0
  -> W1 exists L>0, r>0, L=4r,
       tsupport h ⊂ (r,3r) ⊂ (0,L),
       same pole zeros,
       same negative W self-value.
~~~

The W1 production theorem is

~~~text
Zeta23.ExceptionalZero.exists_strictAperture_poleNeutral_negativeWeilTest_of_offLine_zero
~~~

and the explicit geometry also gives the direct derived collar

~~~text
tsupport h ⊂ (L/4, 3L/4).
~~~

Under the source change of variables `lambda = exp(L/2)`, this centers the support around `u=1` and places it inside the derived multiplicative subinterval `(lambda^(-1/2), lambda^(1/2))` of the full source aperture `(lambda^-1, lambda)`.

The immediate internal priority changed in the W1 post-green pass. Before opening the gamma/digamma channel, test the concrete-zeta zero-side evenization shortcut:

~~~text
W2-ZS / NEXT LEAD
  ZS0  conjugation preserves concrete zeta zeros + multiplicity
  ZS1  build the carrier involution rho |-> 1-rho
  ZS2  gammaOf(1-rho) = -gammaOf(rho)
  ZS3  paperFT(k(-·))(z) = paperFT(k)(-z)
  ZS4  reindex the EF_lit zero sum legally using Summable + Equiv.tsum_eq
  ZS5  prove literatureRHS(half-evenization k) = literatureRHS(k)
  ZS6  conclude W(h,h) = localizedWeilAdditiveRHS(h,h)
~~~

This is a **LEAD / HYPOTHESIS**, not a proved bridge. It is concrete-zeta-specific because `ZeroConfig` itself carries only `rho -> 1-conj(rho)` symmetry. The existing mu/gamma route remains the fallback if any ZS subgate fails:

~~~text
FALLBACK INTERNAL
  I0 pole neutrality -> EF.weilTest h h pole neutrality
  I1 mu/gamma reflection evenness
  I2 weighted gamma-channel integrability
~~~

The source-faithful lane remains active in parallel:

~~~text
SOURCE
  S0 lambda = exp(L/2), 1<lambda, sourceLength lambda = L
  S1 d*u/L²/kappa/q/PsiSharp/QW premise lock
  -> G1-B1B -> G1-final -> G23 -> F1
~~~

If W2-ZS closes, the shortest internal route becomes:

~~~text
W0/W1 [PROVED]
  -> W2-A [PROVED]
  -> W2-ZS direct diagonal additive bridge [OPEN / NEXT]
  -> F0-B
  -> G1-A [PROVED]
  -> F1.
~~~

The source-facing target remains

~~~text
QW_lambda restricted to E_N = canonicalSourceMatrix.
~~~

The preferred K0-K3 finite-wall program after F1 is still planned research, not a theorem-backed terminal reduction.

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
W1 strict finite-aperture recentering with margin         CLOSED / MERGED #81
~~~

Current execution priority:

~~~text
INTERNAL — HIGHEST INFORMATION GAIN
  W2-ZS concrete-zeta zero-side evenization spike          OPEN / LEAD
    rho -> 1-rho carrier equivalence
    gammaOf sign reversal
    paperFT reflection
    summability-safe zero-sum reindex
    direct W self = localized additive RHS

INTERNAL FALLBACK
  I0 pole-neutrality transfer                              OPEN
  I1 mu/gamma reflection evenness                          OPEN
  I2 weighted gamma-channel integrability                  OPEN

SOURCE — PARALLEL
  S0 exact L <-> lambda bridge                             OPEN
  S1 G1-B1B premise/normalization lock                     OPEN
~~~

Continuation if W2-ZS is green:

~~~text
W2-ZS -> F0-B -> G1-A [CLOSED] -> F1.
~~~

Continuation if the zero-side shortcut fails but the analytic channel stays bounded:

~~~text
I0/I1/I2 -> W2-B -> W2-C -> F0-B -> G1-A [CLOSED] -> F1.
~~~

Source continuation:

~~~text
G1-B1B -> G1-final -> G23 -> F1.
~~~

Shared target:

~~~text
F1:
off-line zero
  -> exists L>0, N, u,
     Re(quadraticForm(canonicalSourceMatrix L N) u) < 0.
~~~

F1 is not RH. W2-ZS is not yet a theorem. RH remains OPEN.

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

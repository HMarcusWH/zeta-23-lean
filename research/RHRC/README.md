# RHRC — Riemann Hypothesis Route-Closure harness

RHRC is the research-side control plane for the HMWH Zeta23 fork.

It combines four roles without conflating them:

- **FFBBP-RH**: candidate discovery, null competition, commutation and transfer diagnostics;
- **Permansson-style interventions**: predeclared changes with held-fixed variables and candidate-aligned ablations;
- **OoL-MVS v2.7.6 route closure**: typed evidence semantics, structural route/boundary binding, provenance closure, dependency closure, contradiction and contamination checks;
- **Lean / comparator**: final mathematical certification after a candidate has become an exact theorem.

The terminal target is unconditional RH. The research harness itself is not evidence for RH.

## FFBBP reference contract

The solver layer is bound to **FFBBP Reference Solver Architecture v1.5 (2026-08-19)**. v1.5 supersedes v1.4.2 and changes the RHRC admission logic materially:

- source/target firewall is first-class;
- target leakage and source-side false-field bias are separate gates;
- field existence is distinct from field fit;
- calibration / validation / lockbox separation is mandatory;
- ablation must be candidate-aligned;
- transformed synthetic truth requires projection-consistent oracle scoring;
- local/evolving/regime-switching and multi-shadow sources are legal hypotheses;
- unknown-field diagnostic use requires **V06N known-null + V06P known-positive + relevant V06X artifact rejection** under a frozen profile.

The named RUN42B A0 profile passed the frozen finite synthetic known-truth suite and is therefore available for unknown-field **diagnostic-only** use. This does not validate a real hidden field, advance RH mathematically, or authorize theorem promotion. A material solver-profile change requires requalification. The RH domain adapter must be frozen before a real zeta run.

Machine-readable FFBBP references:

- `ffbbp/FFBBP_REFERENCE.json`
- `ffbbp/configs/run42b_a0_v1_5_qualified_profile.json`
- `ffbbp/configs/rh_adapter_v1.json`

RUN38-era null-immunity settings remain only as regression/pathology references; null immunity alone is no longer an unknown-field admission criterion.

## OoL-MVS v2.7.6 operational contract

RHRC is now bound to **OoL-MVS Kernel v2.7.6 (2026-08-19)** for route-closure operational semantics. We import the governance/evidence machinery, not the kernel's origin-of-life physical claims.

The RH adaptation carries these v2.7.6 laws:

- complete synthetic/adversarial worlds may use two-valued `TRUE/FALSE`, but that mode cannot issue a research/scientific certificate;
- partial research evidence uses strong-Kleene `PASS/FAIL/NA`; missing or unresolved evidence is `NA`, never silently `FAIL`;
- `ClaimResult = PASS|FAIL|NA` is separate from `CertificateStatus = VALID|INCOMPLETE|INVALID`;
- a well-supported negative finding may therefore be `FAIL + VALID`;
- claim-bearing evaluations must bind to raw evidence receipts and the exact support used;
- unconditional-source provenance is positive closure: unknown ancestry is `NA`, and explicit conjectural/conditional ancestry blocks unconditional closure;
- an absence statement such as “no conditional dependency remains” may pass only over a declared complete dependency/provenance search domain;
- discovery may adapt, but confirmatory execution requires frozen route and boundary specification digests;
- a claim-bearing change after lockbox/result exposure requires a new route digest and fresh confirmatory execution;
- route-specific protocols may instantiate but may not weaken these kernel-level semantics.

The supplied v2.7.6 archive and canonical registry hashes are recorded in `ool/OOL_REFERENCE.json`. All six packaged suites were independently rerun from the supplied archive in the authoring environment: **530/530 checks passed**. That is software/formal/numerical verification of the kernel package, not RH evidence.

Current R001/R002/R003 are intentionally still in `DISCOVERY` in `routes/ROUTE_REGISTRY.json`; no fake confirmatory digest is issued while the mathematical objects are still changing.

## Main routes

- `R001_exceptional_zero`: seek a multi-scale observable for which one off-line zero forces positive exponential growth and seek an unconditional prime-side upper bound.
- `R002_multi_probe`: test whether a family of probes separates structures that one finite compression cannot distinguish.
- `R003_ccm_bridge`: require an exact identity/intertwining/controlled limit before connecting finite CCM objects to Weil/Suzuki-style objects.

## Promotion rule

`research/RHRC` -> exact conjecture -> falsification/countermodel pass -> sorry-free Lean -> axiom audit -> comparator topic.

OoL evidence certificates govern integrity of the **research route**. They do not replace Lean/comparator as the authority for mathematical theoremhood.

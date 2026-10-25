# Drafts (no authority)

Files here are unregistered proof drafts. They are not run by `run_candidate_checks.py` or any
workflow, do not change the ledger and create no theorem authority.

Stage 19 installed the force/sampling body into production Consumers and verified it independently
on code commit `59ff485551771c0ab6322562d18fb8e9d4166da4`. Read
[the handover](../STAGE19_HANDOVER.md) and its source-pinned receipts for that authority. The wrapper
below is preserved as the historical draft; its earlier proposed-installation instructions are
retained as provenance.

- `ActualForceSamplingConsumer.draft.lean`: proposed body of the original root
  `Zeta23.OPICAFollowup.actual_force_sampling_consumer` (F1-F3 composed at an actual zero with
  nonreal κ). On 2026-10-24 it compiled without warnings in this standalone wrapper against the
  installed `Zeta23.OPICAFollowup.BoundaryAmplitude` (`lake env lean -DautoImplicit=false
  -DrelaxedAutoImplicit=false <file>`), with `#print axioms` giving propext, Classical.choice and
  Quot.sound only.
  - It uses the Fourier-convention bridge, the actual lattice force and its transform
    (SawtoothForce), the native resolvent and sample identity (NativeResolvent), the spectral
    density (WeightedSpectralMeasure) and the generic boundary amplitude at the right-half-strip
    representative ρ' ∈ {ρ, 1 - ρ} (BoundaryAmplitude).
  - It also uses the not-homogeneous clause (ForcedEuler).
  - To install it, move the `ForceSampling` section into `Zeta23/OPICAFollowup/Consumers.lean` and
    add `import Zeta23.OPICAFollowup.BoundaryAmplitude` there (BUILD_MANIFEST allows it). Then check
    for name clashes and re-verify the existing W01 word/jet consumer in that file. Finally add an
    independent consumer, negative controls, numerics and a stage record as described in
    `tools/stage_record/README.md`.

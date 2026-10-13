# WP5 + WP6 finite research dispositions

**Status:** RH_OPEN. The following are research-producing computations; they do not prove all-K or all-aperture canonical positivity.

## WP5: positive-weight, prime-power-consistent non-zeta countermodel
- Exact-head run [38302040850](https://github.com/HMarcusWH/zeta-23-lean/actions/runs/38302040850), successful job `wp5-modified-prime`, 256-bit Arb, artifact `11771186423`.
- q2 weight `0.490463763049119`, q3 weight `0.607742075660039`, q4 fixed by the **same** prime q2 coefficient divided by sqrt2; q4 inactive at both tested apertures (cutoff Q=3).
- L=259/200=1.295: model even `+8.902990988782997e-7`, model odd `+0.0004243548391040711`, actual-zeta even `+1.766281792752142e-5`.
- L=162/125=1.296: model even `-1.816059327233102e-7`, model odd `+0.0004107051067004576`, actual-zeta even `+1.669751917222927e-5`.
- Certificate scope: pointwise separated Arb signs and scalar-continuity crossing between endpoints; **not** whole-bracket odd positivity, firstness or an RH counterexample.

## WP6: actual native-source negative-shifted K2 ray, report-only
- Exact-head run [38303390271](https://github.com/HMarcusWH/zeta-23-lean/actions/runs/38303390271), successful job `wp6-source-specific-signed-ray`, 256-bit Arb, artifact `11770898559`.
- K2 negative spectral shift μ=−1 is legitimately below the positive odd floors at L=0.15 and L=0.69.
- Complete physical F04 Euler second-source observable on the source-specific shifted ray has opposite certified signs:
  - L=0.15, `Q_ray > 0`;
  - L=0.69, `Q_ray < 0`.
- **FALSIFIED**: `Q_complete(L,Dx(μ)) ≥ 0` on *all* odd-positive negative-shifted K2 rays.
- **Not established**: corresponding sign on the actual selected negative ground, a generated first contact, or RH. Future sign claims must use genuinely additional selected-state information.

Post-green research implication: generic fixed-ray positivity/phase calculus does not distinguish the actual terminal obstruction; pursue contact/ground-dependent *native* signed information, preserving countermodels and different M50/M61 weights.

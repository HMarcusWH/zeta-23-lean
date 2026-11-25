# Compact arithmetic extraction v0.6 — source custody only

Pinned Apache-licensed rewrite: lsernau/grh-lean 72fead102f663d5c7a407964a13dc0cf9d977207, tree 5eb1240f03e791edd3fc7aa84a3a7d8dc3997b7f.
Native reference: 347c89e926a0f335caaab13d005ea738b80ee34b (#317). This isolated branch does not change the active PR, main, claim registry, or native Lean proof.

The live source tree lock covers every tracked blob in both editions, including notices and attribution. The workflow verifies bytes against Git identities, computes import closures and lexical declaration candidates, preserves the complete source archive, and creates independent candidate source-only arithmetic cuts before New.grh / the public terminal theorem. The readable and compact cuts are distinct; neither is yet compiler-certified. Lexical declaration anchors are not proof-value edges. No original large-proof or 27 analytic-port source is redistributed in this extraction.

Cut targets:
- compact New.ArithmeticOnly, containing star_inequality and eventually_primeError_le_rpow;
- readable New.Reduction.ArithmeticOnly, containing New.eventually_primeRemainder_le_rpow.

The conditional quadratic-twist criterion remains an allowed analytic consumer, with a fixed conductor-one target at modulus 18480 and class 9239. Do not identify the weighted prime statistic with the literal native ramp. See v0.5 paper bridge for the finite-tolerance zero-strip and smoothed contour transfer. An unconditional upstream RH/GRH theorem is forbidden as an input to the native supplied route. This workflow runs no Lean build and promotes no theorem. Next gates: inspect the two source slices, build under Lean 4.35.0 and exact Mathlib pin, collect full proof-value/type/structural closures and axiom audits, independent replay, native pin compatibility, literal ramp transfer, then full claim validation. RH_OPEN.

Local reproduction: clone the upstream repository at the lock, then run python extract_all.py --source /path/to/clone --out /path/to/empty/output. The emitted archives and receipts are evidence, not proof.

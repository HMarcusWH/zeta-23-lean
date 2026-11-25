# OPICA terminal proof candidate — 2026-11-25

**Status: SOURCE_IMPLEMENTED_CANDIDATE / NOT KERNEL VALIDATED / RH_OPEN.**
Base: native #311 head 4f81c784d3b330395507f6dcd1c8b0010b3835cc, not merged authority.
This work is explicitly arithmetic-supplied, not an independent rediscovery of
Alpöge's arithmetic, and not independent Step 4 closure.

## Mathematical change

Instead of reimplementing the signed-cosine phase argument, use the original
generic conditional Landau window theorem on a strictly later subwindow.
For a fixed exponent h and a zero to the right of theta, choose
1 < c < 3/2 and h < c(2 theta - 1). If arbitrarily late full literal
energy windows had E(Y) <= Y^h, put Z=Y^c and delta'=3/(2c)-1.
The subwindow [Z,Z^(1+delta')] is [Y^c,Y^(3/2)]. With R=max(G,0),
the weighted Young inequality gives

    2 R(x) x^(-theta-1)
       <= E_density(x)/Y^h + Y^h x^(-2 theta).

Integrating on the subwindow gives at most 1 + Y^h Z^(1-2 theta)/(2 theta-1)
for the doubled integral. The second term tends to zero. Thus the generic
analytic WindowHyp holds for every positive eta, contradicting the pole to
the right of theta. This proves the candidate eventual lower bound
E(Y) >= Y^h for every 0<h<3a, where a is the actual nonattained-safe strip
supremum. It avoids the stronger O(x) growth lemma: original poleData uses
O(x^2), which suffices for the generic window proof. The original T02/T03
signed-phase derivation is not separately implemented.

Both parity slices follow from the existing zero-strip floor and monotonicity,
with delta=a/2 and rate 5a/4 when a>0. If a=0, use only the conditional
critical-line floors. No arithmetic upper enters this native comparison.

## Attribution and source boundaries

Analytic source: Alpöge/Claude, original source as mirrored in
HMarcusWH/riemann-hypothesis at 40e56bab026552e089d7afcfeff08d2defb9c005.
The source manifests enumerate exact original blob IDs and import-only edits.
The supplied Jimmie Adriazola reconstruction, pp. 8–11, motivates the analytic
route; it is not proof authority. R1/R2 adapter source is pinned to
7026cc4b8b2cee4e64fce998782f00b6fed4bb7f. The original source's licensing
terms need confirmation before release; this draft does not assert a license.

The common workspace stages tracked native source into the original v4.33.1
Lake environment, replaces port-module imports by identical original analytic
modules, and removes the known terminal consumer declarations from the source
files of the original arithmetic import chain. The generic conditional Landau
lemma is not the original unconditional RH/GRH endpoint.

ClosedPrincipal follows the exact original literature argument assembly from
MainConclusion, EveryCharacterOfLiteratureOfVWin,
SiegelEisensteinSecondTermHypotheses and TopPlug, stopping at TopG.
The original host is specialized to PChar.one. The final tracked source
calls principal_ramp_windows_proved, native_energy_of_ramp_windows,
directEnergyToC1_proved, and the original native C1 consumer in one environment.

## Validation

- Native standalone: lake build Zeta23.OPICATerminal.AuditNative.
- Original-pin staged: stage_common.py then build Zeta23.OPICATerminal.AuditNative
  and OPICATerminalSupplier.AuditTerminal (never use cross-pin .olean files).
- Audits: literal expected types, transitive standard-axiom restriction,
  proof-value dependency closure with structural inductive links, required
  native C1 and arithmetic dependencies, forbidden original terminal calls,
  supplier-free native proof roots.
- Source slicing and import checks are additional engineering controls, not
  substitutes for the kernel or independent checker.

Independent replay, complete anti-circularity review, original all-lane
acceptance, canonical materialization, and full workflow harvest remain
mandatory and OPEN. Neither a successful build of a conditional theorem
nor a source-only root is an accepted RH theorem. No registry changes made.

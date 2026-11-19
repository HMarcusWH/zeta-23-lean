# Geometry/floor routes versus the current fixed-source target

10 November 2026. Read-only comparison against the current-source snapshots at PR299 `b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7`. No new theorem, compiler run, numerical replay or repository change. Exact statements were reread in `GrowthClosure.lean`, `CofinalSemiboundedClosure.lean` and `GeometryReconstruction.lean`; related proof audits were compared. This report recommends research allocation, not a probability of proving RH.

## Recommendation

Do **not** select SG/PG or SB merely because their terminal floors look less demanding than vanishing error. They improve the logical target, but they do not supply the arithmetic needed to reach it. Based on the presently paid interfaces, I favor the **latest fixed genuine-source prime estimate** as the main route, subject to the companion arithmetic review choosing its exact weighted-L1 or signed-residual form. It concerns one fixed source and allows cofinal horizons. The geometry route instead requires bounds over a growing vector family and, in SG, two different unproved source estimates.

Keep SB/PG as a precisely specified alternative if a new native inequality emerges. Use A10 to test how a finite response mechanism behaves, without treating its rank as evidence of a uniform law. This recommendation is not a theorem that the prime route is easier or that all full-source geometric implications have been exhausted.

## Exact alternatives and their cost

| Route | Independent premise | What makes it attractive | What prevents promoting it to the main route now |
|---|---|---|---|
| SB | One fixed `C>=0`; for every R, some `L>max(R,2)` has an entire even or odd physical moment slice bounded below by `-C||u||²`, at `K=ceil(L^4)`. Parity may depend on L but not on u. | No vanishing error, no all-late upper, no fixed parity. Existing all-late arbitrary-depth contradiction is exact. | Still a uniform absolute bound over a whole growing slice. No independent source inequality fixes the common spectral level. A finite L4 certificate does not approach its unbounded quantifier. |
| PG | Fix one parity, C, natural d and L0; for every `L>=L0`, the entire slice has floor `-C(1+L)^d`. | Any fixed polynomial loss is acceptable; useful with crude geometry bounds. | Every late aperture and every slice vector remain required. This is a different tradeoff from SB, not a straightforward weakening of it. |
| SG→PG | Complete native geometry basis and gap, absolute diagonal floor, full mixed-response norm and leakage bound produce a polynomial floor. | Rank-two reconstruction and physical norm transport already exist. Geometry costs are polynomial. | Two genuinely open arithmetic slots, plus formal adapters for the paper gap/basis estimates. It is sufficient, not shown necessary for PG. |
| C1/A10 scaling | For every n, aperture `L>=n+2` with whole-slice floor `-1/n`; exact finite certificates can supply individual instances. | Concrete finite representation and checker work. | Stronger accuracy than SB. A10 fixes L4/K256 and its 125/128 split; rank 7 is optimal only in that frozen scalar-pivot family. No uniform rank, gap, conditioning or signed-source estimate follows. |

The primary source definitions are [SB](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/OPICARound4/ArithmeticFrontier/CofinalSemiboundedClosure.lean#L220), [PG](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/OPICARound4/ArithmeticFrontier/GrowthClosure.lean#L101), and [SG](https://github.com/HMarcusWH/zeta-23-lean/blob/b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7/Zeta23/OPICARound4/ArithmeticFrontier/GeometryReconstruction.lean#L318).

## A quantifier trap: cofinal polynomial control is not already a consumer

`GrowthClosure` produces exponential-depth negative witnesses at **cofinally many** apertures, independently for the two parities. `CofinalSemiboundedClosure` proves negative witnesses in **both parities at every sufficiently large aperture**, but only for a depth M fixed **before** choosing that threshold.

These results do not automatically imply an RH consumer for polynomial floors on an arbitrary cofinal subsequence. One cannot set M equal to `C(1+L)^d` after L is selected. Nor may two cofinal sequences be presumed to meet. A cofinal-polynomial refinement would need a quantitative depth-to-aperture transport or another common-horizon theorem. It is not an already proved consequence of the displayed statements. This is a quantifier obstruction to that proposed deduction, not a counterexample to the actual conjectural floor.

## What SG would need, completely explicitly

Fix even parity to avoid gratuitously adding the distinct odd M3-normal component. At each large L, retain the full actual source operator A, physical slice S, unit leakage normal w, geometry `G=P_S D0|S`, complete orthonormal eigenbasis v_i, and all prime powers. Let

`R(u)=exp(-u/2)(psi(exp u)-exp u)`.

The current paper adapter writes the genuine complete discrepancy action as

`D_R f(t) = integral_0^t R(u)[f'(t-u)+f(t-u)/2]du`

`             - integral_0^(L-t) R(u)[f'(t+u)-f(t+u)/2]du`.

The actual source formulas are

`<v_i,A v_i> = <v_i,(-A_arch+T-2I)v_i> - <v_i,D_R v_i>`,

`z=P_S A w = P_S(-A_arch+T)w - P_S D_R w`,

where `T f(t)=integral_0^L exp(-|t-s|/2)f(s)ds` and `||T||<=4`. Both histories remain. The local `2w` term disappears only because `P_S w=0`.

One sufficient pair of **new arithmetic theorems** would be constants A0,B0,a,b,L0, fixed independently of later L, such that for all `L>=L0`:

1. `Re <v_i,D_R v_i> <= A0(1+L)^a` for **every** actual geometry eigenvector;
2. `||P_S D_R w|| <= B0(1+L)^b` for the **complete** projected response.

The first is one-sided signed work; the second is a two-sided norm bound. Bounding one does not supply the other. The independently polynomial reference, `||ell||<=K²` and the paper gap `g>=c_geo K^(-241)` then make

`h0 - 2||z||||ell||/g`

a polynomial lower floor. The severe gap exponent is acceptable for PG; making it sharp is not the decisive arithmetic task. Formal basis, gap and source adapters would still need to populate the existing certificate. No individual complementary zero, prime power, projected component or inherited history may be dropped.

This gives a concrete research target, but it does not establish either estimate. Absolute PNT-error envelopes still cost an exponential. Fixed derivative norms, endpoint moments, the source's rank-two commutator and normal-filter visibility do not bound this signed action.

## Why the accumulated ground constraints do not yet supply SG's absolute anchor

The valid actual-source composition in [SOURCE_COUPLING_APPLICABILITY_12](../step4-study-2026-11-09/SOURCE_COUPLING_APPLICABILITY_12.md) proves

`h_i >= lambda_odd - 2K(1+2K²/g)||z||`.

This is a bound relative to the actual odd bottom at the same L,K. Even a polynomial z bound leaves that bottom unpaid. The strict-even ground ray, strict-odd reciprocal even input, geometry basis vector and smooth original detector cannot be interchanged. The tied-ground record retains singular kernels and full complements; it does not provide a uniform inverse through a tie. Its parity-producer cutoff also cannot simply be identified with the quartic detector cutoff.

The derivative/source/trace identities constrain relative motion. The fixed-geometry falsifier retains actual derivative geometry and the compressed commutators while allowing arbitrary spectral scale, but changes the genuine arithmetic source. It therefore proves that the retained algebra alone does not anchor the absolute level; it does **not** refute the complete native-source constraint set. See [SOURCE_DERIVATIVE_TRACE_OBSTRUCTION_13](../step4-study-2026-11-09/SOURCE_DERIVATIVE_TRACE_OBSTRUCTION_13.md).

The trace calculation makes one concrete signed source scalar explicit, but a polynomial bound on that relative trace difference would still need an absolute-ground bridge. Its actual test has an exponentially large absolute terminal prime mass, so absolute weighting loses precisely the needed cancellation. See [ACTUAL_TRACE_SOURCE_TEST_14](../step4-study-2026-11-09/ACTUAL_TRACE_SOURCE_TEST_14.md).

## How A10 and the geometry discoveries should support the selected main route

A10 provides an optimized finite representation and the correct weighted error metric. It can guide an experiment about whether a mechanism persists. Before any scaling inference, qualify the exact native-entry/physical-Gram bridge and inspect the different L5 data. It is not the same object as the geometry leakage response z or the optimal-probe innovation pairing.

The exact geometry-normal transform shows an isolated off-axis mode is visible. The complete critical-line zero contribution has a paper polynomial bound on actual moment vectors. Other off-line contributions remain, with phases and multiplicities. These observations support falsification of an attempted mode-hiding argument; they do not supply an independent source upper. A fresh attempt to control that complement is another version of the missing arithmetic problem, not an already paid route.

The most useful contribution of these routes to the current focus is therefore a precise specification of the shared problem: **the complete signed source must have an independently controlled absolute level or response, not merely recoverability, relative coupling, or isolated-mode visibility**.

## Focus decision

Primary: the fixed genuine-source arithmetic route, where the newest reductions have already removed unnecessary source sectors and paid the model. Select its least demanding exact sufficient upper, retain its same-horizon quantifiers, and attack the signed cancellation using genuine arithmetic identities.

Reserve: SB if an absolute constant floor becomes directly available; PG/SG if actual source estimates naturally produce polynomial losses. Do not complete every geometry or certificate branch as a prerequisite to the prime estimate. Promote the reserve only when a new theorem pays an identified arithmetic slot, rather than because another finite example is green.

Step 4 and RH remain OPEN.

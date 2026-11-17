# Post-PR300 K=5 mixed-source audit — frozen candidate contract

**Status:** DRAFT / research proposal. **Base:** accepted #299 merge
`df914f38f26bdc4109aeaa13f48b3896c3bc61b1`.
**Dependency:** PR #300 parity exact sequence is not yet merged or release-qualified.
**Claims:** Step 4 OPEN; RH OPEN. Finite Arb observations are not Lean theorems.

## Motivation and exact algebra

At K=5 the fixed quartic odd seed has dimension 1 and the fixed even
seed has dimension 2, by the source declarations compiled on PR #300.
This is *not* a parity-energy equivalence. The physical diagonal is
`D_n = beta + n^2`, `beta = (L/(4*pi))^2` (do not drop D).

Use the following rational seed coordinates on centered indices [-5,5]:

- Even center lift `e_0=1`; `e_1..e_5=(-4/5,2/5,-4/35,1/70,0)`,
  extended evenly.
- Odd seed `v_0=0`; `v_1..v_5=(42,-48,27,-8,1)`,
  extended oddly; use `t_n=n*v_n`.

Exact rational arithmetic verifies `M_0=M_2=M_4=M_6=0` on both
even vectors, `M_1=M_3=M_5=M_7=0` on v, and `e_0=1`, `t_0=0`.
The ordered physical frame is `[D*t,D*e]`.

For the physical Gram `G_ij=<D*frame_i,D*frame_j>`, exact polynomials:

- `G11=44*(845 beta^2+10426 beta+43565)`
- `G12=-88/35*(65 beta^2+442 beta+1205)`
- `G22=33/2450*(195 beta^2+416 beta+640)`
- `det G=3146/49*(1105 beta^4+16354 beta^3+88785 beta^2+124000 beta+114400)`

Thus the mixed Gram is strictly negative, and Gram is positive definite,
for positive beta. These are independently checkable **exact rational
calculations**, not separately imported Lean declarations.

## Actual source and quotient

Take the **production** canonical matrix from
`research/RHRC/routes/R003_ccm_bridge/canonical_source_arb.py`,
not a newly normalized or modified proxy. Let `H=X^* M(L,5) X`,
where `X=[D*t,D*e]`. Let `G=X^* X` in the same frame.

For each `eps>=0`, compute `H_eps=H+eps*G`. If `a=(H_eps)11`
is certified strictly positive, report the Schur residual
`S_eps=(H_eps)22 - |(H_eps)12|^2/a`. Otherwise report the odd
block sign and leave Schur evaluation unasserted. A center-lift change
`e -> e+t*c` does not change the Schur residual (exact scalar algebra);
the code includes a lift consistency residual, but only the exact
algebra test gives a universal lift identity.

This is a **2x2 finite research observable**. Its sign is not automatically
a source-specific bound. No K=5-to-all-K transfer is established. The
cutoff-3 scalar obstruction of #299 does not belong to the quartic
moment slice.

## Frozen probes and falsification

Frozen points: `L=2,Q=7, gamma=5,delta=1/4` and
`L=3,Q=20, gamma=5,delta=1/2`, both `K=5`, outward Arb at 192 bits.
The backend verifies each cutoff cell. The ablation removes the most recent
*included prime power* (7 at L=2, 19 at L=3), never a nonexistent atom at Q=20.
An independent mpmath exploration suggested the second synthetic off-line case
may have negative Schur residual, while the real canonical case remains
positive. This is a **LEAD / NONCERTIFIED** and must be confirmed or rejected
by the Arb workflow, not treated as established evidence. Test precisely:

1. Actual canonical prime source.
2. Same source with the most recent included prime power removed.
3. Same source with that prime-power weight increased by one quarter.
4. Synthetic on-line zero-side increment (gamma=5, delta=0).
5. Synthetic off-line zero-side increment (gamma=5, delta=1/4 at L=2 and delta=1/2 at L=3).

Controls 4-5 use the existing `planted_increment` **only as a synthetic
zero-side falsifier**. They do not construct alternate zeta functions
or globally consistent Euler products. The modified-weight probe is
also not the genuine prime sequence.

All numerical signs must be determined from rigorous Arb enclosures;
unknown/overlapping intervals remain unresolved. No finite scan is a
proof of absence of a first crossing or an all-aperture inequality.

In the V2 JSON format, finite `lower` and `upper` use exact rational
strings for the directed Arb endpoints. Parse them as fractions, including
integer strings for whole endpoints. V1 endpoint strings used rounded
decimal display and should be treated as display values. The finite
sign classifications are computed directly from the Arb balls.

## Acceptance and release rules

- Exact algebra tests must pass without external packages.
- The source probe must produce a machine-readable record of actual
  canonical and control blocks; source/sign diagnostics are frozen as
  CI artifacts, not automatically promoted to a claim registry.
- A plausible inequality must be attacked with the controls before
  any theorem PR is opened.
- **A positive K=5 scan is not Step 4 closure.** An RH-relevant result
  still needs a genuine-prime signed estimate and a source-preserving
  all-parameter (or rigorously adequate detector) implication.
- The workflow uses inherited SHA256-pinned FLINT and SymPy environments and tests the two observed opposite synthetic off-line signs as **finite research regression**, not a zero theorem.
- Before merging this branch, establish a *separate independently
  reviewed* source-scope policy and account for all inherited gates.
  Do not mutate #299 V1 acceptance, #300 pending source policy,
  formal claims, or generated RHKG outputs merely to make CI green.

## Navigation

- Runner: `post300_k5_mixed_source.py`
- Exact tests: `test_post300_k5_mixed_source.py`
- Dedicated research workflow: `.github/workflows/rhrc_post300_k5_research.yml`
- Live authority: PR #299 merged; PR #300 draft pending acceptance.

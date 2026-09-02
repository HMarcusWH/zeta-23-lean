# R003 — CCM / finite Weil bridge

Status: **ACTIVE DISCOVERY ROUTE. INTERNAL F1 + K0-F1 + K0-F1E PROVED. RH OPEN.**

## Current authority

~~~text
theorem-state anchor = PR #98 merge 4f212e35fefb339646e294573dcb390dae2f6181
theorem tree = 84a678327fffe6806e1e786ac2e159a5ce628f67
final validated head = 723c63badb2ac787c3dfa78369909477af6bc6a4
RHRC #685 = SUCCESS
Permansson #458 = SUCCESS
RH = OPEN
~~~

## Closed internal ladder

~~~text
W0/W1/W2-ZS + G1-A                                    PROVED
F0-B1A/B1B/WCONT/F0-B1C-A/B                           PROVED
strict finite sign transfer + F1                      PROVED
K0-F1 constrained algebra / Hermitianity / displacement PROVED
K0-F1E rank, N>=2, Euclidean sector and quadratic bridge PROVED
K0-F1E constrained Euclidean negative direction       PROVED
~~~

## #98 production endpoint

Off-line zero -> L>0, N>=2 and a nonzero x in euclideanBoundaryFlatSubspace N with Re <M_N(L)x,x> < 0.

No compressed eigenmode, positivity theorem or RH theorem is asserted.

## Next: exact centered nesting

Use iota(i).val=i.val+(M-N), prove centeredIndex preservation and exact principal-block nesting, then raw/Euclidean zero-extension preservation and quadratic persistence.

Exact nesting is an admission condition; approximate nesting is not a silent substitute.

## Then: parity and constrained spectrum

Use Fin.rev, prove exact parity dimensions, then build the constrained subtype operator with orthogonalProjectionOnto and extract a negative constrained eigenmode.

At the first bad parity size, the intended new constrained shell should be one-dimensional only after the parity dimension theorem is established.

## Schur/secular firewall

Historical FTI-C1 used an ambient coordinate-shell Schur complement. The post-#98 route uses the orthogonal complement of the embedded constrained parity sector inside the larger constrained parity sector. They are not identical without a theorem.

## KKT firewall

Codimension three alone does not justify the residual equation. First prove V_N^perp = span{1,d,d²}.

## Source and dead-route firewalls

OBS-015 remains permanent. G1-B1A is proved; G1-B1B/G1-final/S-NEG/G23 remain open.

DR-010 remains dead. The generic divided-difference displacement identity is diagonal-blind, so low displacement rank alone cannot control absolute sign/inertia.

## Current post-green records

- K0F1E_POST_GREEN_EUCLIDEAN_RESET_2026_09_02.md
- ../../RESEARCH_LEADS_POST_98_DELTA.md

**RH remains OPEN.**

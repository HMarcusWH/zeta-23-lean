# R003 — CCM / finite Weil bridge

Status: **ACTIVE DISCOVERY ROUTE. INTERNAL F1 + K0-F1 + K0-F1E + N-FLOW PROVED. RH OPEN.**

## Current authority

~~~text
theorem-state anchor = PR #100 merge 4427e2a8c8d90dbb7d66d9d96f9a410cecb75df9
theorem tree = 705ab8b88728a5b90d850eb4b51c01a66811f088
final validated head = 497adcd6a746d49fd23654cabf4ed8f0c58db8a9
RHRC #691 = SUCCESS
Permansson #464 = SUCCESS
axioms = [propext, Classical.choice, Quot.sound]
sorryAx = absent
RH = OPEN
~~~

## Closed internal ladder

~~~text
W0/W1/W2-ZS + G1-A                                      PROVED
F0-B1A/B1B/WCONT/F0-B1C-A/B                             PROVED
strict finite sign transfer + F1                        PROVED
K0-F1 constrained algebra / Hermitianity / displacement PROVED
K0-F1E rank, N>=2, Euclidean sector and quadratic bridge PROVED
K0-F1E constrained Euclidean negative direction         PROVED
N-FLOW exact centered principal-block nesting            PROVED
N-FLOW all centered moments / finite function preserved  PROVED
N-FLOW Euclidean constrained isometric zero extension    PROVED
N-FLOW fixed-L persistent negative tail                  PROVED
~~~

## #100 production endpoint

Off-line zero -> one fixed L>0 and N0>=2 such that every M>=N0 has a nonzero x in euclideanBoundaryFlatSubspace M with Re <M_M(L)x,x> < 0.

No compressed eigenmode, parity theorem, positivity theorem, finite-to-infinite theorem or RH theorem is asserted.

## Immediate post-#100 consequence

For fixed L, badness defined by existence of a negative constrained direction is upward persistent under N. Therefore a nonempty bad-size set has a least global bad N.

Combined with finrank V_N = 2*N-2, the total new constrained shell from N to N+1 has dimension two. This is a derived consequence to theorem-lock; it is not yet a promoted project theorem.

## Next: parity and constrained spectrum

Use Fin.rev to prove centered-index reversal, simultaneous canonical-matrix reversal invariance, moment parity, displacement-vector oddness, constrained-sector invariance, compatibility with the #100 embedding, and exact parity dimensions.

Expected for N>=2:

~~~text
finrank V_N^even = N-1
finrank V_N^odd  = N-1
~~~

Only after these dimension theorems may the total 2D increment be described as one even plus one odd new constrained dimension.

Then build the constrained subtype operator with orthogonalProjectionOnto and extract a negative constrained eigenmode using finite-dimensional Rayleigh theory.

## First bad shell

Global first bad N is available before parity at the consequence level. Parity should refine the first bad state to a first bad parity sector with a one-dimensional new constrained shell.

That one-dimensional shell is the intended entry point for a scalar constrained secular equation.

## Schur/secular firewall

Historical FTI-C1 used an ambient coordinate-shell Schur complement. The post-#100 route uses the orthogonal complement of an embedded constrained sector inside the larger constrained sector. They are not identical without a theorem.

Principal-block nesting also does not imply full operator intertwining or literal nesting of the compressed operators.

## KKT firewall

Codimension three alone does not justify the residual equation. First prove V_N^perp = span{1,d,d²}.

## Source and dead-route firewalls

OBS-015 remains permanent. G1-B1A is proved; G1-B1B/G1-final/S-NEG/G23 remain open.

DR-010 remains dead. The generic divided-difference displacement identity is diagonal-blind, so low displacement rank alone cannot control absolute sign/inertia.

Finite-to-infinite convergence remains dormant: #100 proves exact finite nesting, not any infinite limiting theorem.

## Current post-green records

- K0F1E_POST_GREEN_EUCLIDEAN_RESET_2026_09_02.md
- ../../RESEARCH_LEADS_POST_100_DELTA.md

**RH remains OPEN.**

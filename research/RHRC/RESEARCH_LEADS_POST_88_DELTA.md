# RHRC research leads — post-PR #88 delta

> **Claim firewall: RH remains OPEN.**
>
> This file supplements the full historical RESEARCH_LEADS.md ledger. It records only state changes caused by the exact green F0-B1B theorem head. The full ledger remains the history-bearing inventory. Historical post-#86 delta files are not rewritten.

## Validation snapshot

~~~text
merged main = 1ad066f0a263725ea7b84447a637fcebda78e9ca
merged through = PR #87

PR #88 theorem head = 5e943d8cd6825c3c649198c52d90d1ed5d8d8b47
synthetic merge = 9eb9281394684600b35a58ce2cb3c757d06379cc
RHRC #609 = SUCCESS
Permansson #382 = SUCCESS
PR status at documentation time = OPEN / NOT MERGED

RH = OPEN
~~~

## L-F0B1B-01 — exact three-mode boundary-flat projection

**Research status:** PROMOTED ON GREEN THEOREM HEAD  
**Formal status:** PROVED on exact #88 head; pending permanent merge

For N>=1, arbitrary centered finite coefficients can be corrected exactly on modes -1,0,+1 so centered moments 0,1,2 vanish.

The projection is theorem-locked as:

~~~text
boundaryFlatProject_boundaryFlat
boundaryFlatProject_eq_self_of_boundaryFlat
boundaryFlatProject_idempotent
~~~

The endpoint/moment identities are also exact.

This closes the algebraic legality seam in the primary F0-B1 route.

## L-WCONT-01 — family-level W continuity

**Research status:** ACTIVE / LOAD-BEARING / NEXT  
**Formal status:** OPEN

The post-#88 refinement is to avoid a generic family-dominated-convergence theorem if one quantitative bilinear bound suffices.

Use the asymmetric W2-A regularity plus inverse-square zero summability.

Candidate theorem:

~~~text
common compact support envelope
+ f C²
+ g continuous

-> |W(f,g)|
   <= K_Λ * (||f||_1 + ||f''||_1) * ||g||_1.
~~~

Exact norms/constants are not fixed until proved.

Falsifier: the complex gamma-strip Fourier estimate or the required family-independent support constant fails to close cleanly.

## L-WCONT-XTERM-01 — diagonal continuity by cross terms

**Research status:** ACTIVE SUPPORT  
**Formal status:** LEAD / HYPOTHESIS

If the bilinear WCONT-A estimate is proved, try

~~~text
e=p-h
W(p,p)-W(h,h) = W(e,p)+W(h,e)
~~~

to reduce diagonal convergence to one small first-leg error plus bounded L¹ control.

Must theoremize or justify W linearity/conjugate-linearity and tsum rearrangements. Do not assume the identity is available merely because W is defined as a tsum.

## L-F0B1C-01 — projection-smallness from endpoint residuals

**Research status:** ACTIVE / AFTER WCONT-A  
**Formal status:** OPEN

PR #88 proves exact endpoint/moment identities. Use them to convert

~~~text
q_N(0) -> 0
q_N'(0) -> 0
q_N''(0) -> 0
~~~

into

~~~text
M0(q_N) -> 0
M1(q_N) -> 0
M2(q_N) -> 0.
~~~

Then prove the three fixed correction coefficients and the interior correction go to zero in the topology selected by WCONT-A.

Permanent caveat: the correction alone is not generally boundary-flat and is not automatically a global C² hard-window test.

## L-F0B1-APPROX-01 — strict-collar finite Fourier approximation

**Research status:** ACTIVE / WAITING ON WCONT-A  
**Formal status:** OPEN

Do not formalize a textbook-wide density theorem.

Target only:

~~~text
h C²
tsupport h strictly inside (0,L)

-> raw finite Fourier q_N
   converging in the exact WCONT-A topology
   with endpoint jets tending to zero.
~~~

Exploit that W1 gives an actual collar where h is identically zero.

Pinned Mathlib has no currently identified ready Fejer theorem for this load-bearing step.

## L-BKILL-01 — fixed boundary-killer multiplication

**Research status:** READY FALLBACK  
**Formal status:** LEAD / HYPOTHESIS

The proved five-mode pattern of

~~~text
(1-cos(2πx/L))^2
~~~

remains an alternative way to enforce endpoint jets while preserving finite Fourier structure.

Projection is now preferred because its exact algebra survived Lean and only changes three fixed modes.

## L-F0B2-01 — direct localized-additive continuity

**Research status:** DORMANT / READY FALLBACK  
**Formal status:** OPEN

#88 further weakens the reason to prefer this route. Reactivate only if WCONT-A or projection-smallness grows disproportionately large.

## L-W0-02 — witness regularity strengthening

**Research status:** DORMANT / READY SUPPORT  
**Formal status:** LEAD / HYPOTHESIS

The current C² witness remains sufficient until an actual WCONT/approximation proof demonstrates otherwise.

## L-KRYLOV-01 — three-moment kernel versus displacement

**Research status:** READY FOR POST-F1 INVESTIGATION  
**Formal status:** LEAD / HYPOTHESIS

A primary-route F1 witness should retain

~~~text
1^T u = 0
1^T D u = 0
1^T D²u = 0,
~~~

while

~~~text
D M - M D = g 1^T - 1 g^T.
~~~

#88 makes this more relevant because the constraint-preserving path to F1 is no longer hypothetical.

Still no spectral/crossing consequence is proved.

## Updated priority

~~~text
1. WCONT-A quantitative bilinear bound
2. diagonal continuity / cross-term corollary
3. finite Fourier approximation matched to that bound
4. endpoint residual -> moment residual control
5. projection-smallness
6. strict finite sign transfer
7. strengthened boundary-flat F1
8. post-F1 review / v2.0 / K0-K3
~~~

Parallel source route remains S-GEOM / S-IFACE / G1-final / S-NEG / G23 under OBS-015.

RH remains OPEN.

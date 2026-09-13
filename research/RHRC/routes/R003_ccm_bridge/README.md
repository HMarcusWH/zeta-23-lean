# R003 — CCM / finite Weil bridge

Status: **ACTIVE. THEOREM AUTHORITY THROUGH PR #159. EXACT MOMENT-PREFIX JETS + SIGNED RIESZ BOUNDARY RECURRENCE ARE CLOSED; CURRENT FRONTIER = SAME-STATE SHIFTED RIESZ × CROSS-PARITY SOURCE COMPOSITION. RH OPEN.**

## Current authority split

```text
live main after merged PR #159 = 63862cd80501754c6c6599ffea09b874a327dae4
live main tree = cb7a81d3b10e7f909b794103f2a919a3a3ccf233
latest theorem-bearing PR = #159
validated theorem head = b2a064ad5d1f0acbd93309a9257c5661cfa3ec28
validated theorem tree = cb7a81d3b10e7f909b794103f2a919a3a3ccf233
RHRC #1021 / run 34736245287 = SUCCESS
Permansson #794 / run 34736245311 = SUCCESS
control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

## Closed internal ladder

```text
finite canonical obstruction / Euclidean wall                   PROVED / #94-#98
N-flow + parity + first-bad + Schur/secular                     PROVED / #100-#128
source-explicit cross-parity transfer                            PROVED / #129
exact canonical source-moment decomposition                      PROVED / #131
zero-shift source transport / absolute energy / determinant      PROVED / #134-#137
regular selected first-bad endpoint                              PROVED / #140-#150
retained first-bad + exact pole-prime discrepancy                PROVED / #153
legal generic Riesz smoothing + parity/even jets                 PROVED / #155
complex production D transport + exact Riesz 6/even 8            PROVED / #157
retained transformed negativity + ExceptionalZero R6 wrapper     PROVED / #157
general moment-prefix odd-jet law                                PROVED / #159
exact seventh / even ninth leading-moment self-energy jets        PROVED / #159
generic signed complete-channel Riesz boundary recurrence        PROVED / #159
retained R6->R7 / even R8->R9 moment-square boundaries           PROVED / #159
```

## Exact #159 production surface

Validated declarations include:

```text
iteratedDeriv_one_sourceAtomRealEnergy_eq_two_normSq_sum
iteratedDeriv_odd_sourceAtomRealEnergy_eq_moment_normSq_of_prefix
iteratedDeriv_seven_sourceAtomRealEnergy_eq_moment_three
iteratedDeriv_nine_sourceAtomRealEnergy_eq_moment_four_of_even_boundaryFlat
canonicalPolePrimeRieszEndpointScalar
canonicalPolePrimeRieszBoundaryTerm
canonicalPolePrimeRieszEnergy_eq_succ_add_boundary
canonicalRieszSourceChannelEnergy_eq_succ_add_boundary
```

The boundary term is signed; no positivity of the endpoint scalar is asserted.

On retained first-bad states #159 additionally proves exact R6/R7 and, for even retained parity, R8/R9 decompositions. The vector dependence of the first surviving even boundary correction is compressed to `normSq(M4)`.

## Post-green composition with existing R003 theorem inventory

The route already contains exact negative-shift cross-parity transfer. At an even secular root:

```text
cubicSecularScalar .odd ...
  = overlap * evenQuadraticSourceMoment L (N+1) evenShiftedTrial.
```

The same source moment is theorem-backed as

```text
evenQuadraticSourceMoment
  = explicitCanonicalSourceMoment
  = pole
    - reduced arch diagonal
    - reduced arch offdiagonal
    - finite weighted source atoms.
```

Global first-bad minimality also supplies predecessor nonnegativity for an arbitrary chosen parity at every smaller size.

These facts predate #159. The new opportunity is to put them and #159's Riesz boundary structure on the **same even negative secular trial**.

## Current frontier — FB-04B same-state composition

Preferred next theorem package:

```text
negative eigenmode -> ParityBad
first-bad predecessor nonnegative for either parity
same even secular root -> exact negative complete Riesz-8 state
same even secular root -> exact Riesz-9/M4 boundary inequality
same even secular root -> odd secular scalar = overlap * explicitCanonicalSourceMoment
```

Then prove the fail-closed fork

```text
odd successor ParityBad
OR
explicitCanonicalSourceMoment(even negative secular trial) != 0.
```

If the odd successor is assumed good, the theorem may strengthen this to nonzeroness of both the odd secular scalar and the product factors, without dividing by them.

## Next lead — mixed quadratic-normal source jet

**Status: DERIVED / OPEN IN LEAN.**

Define the elementary mixed observable

```text
h_v(omega) = <centeredQuadraticNormal, sourceMatrix(omega) v>
             / <centeredQuadraticNormal, centeredQuadraticNormal>.
```

For even boundary-flat `v`, the post-green calculation predicts

```text
h_v^(7)(0) = -2*(2*pi)^6*M4(v).
```

If theoremized, this would connect the linear source defect used by cross-parity transfer to the quadratic `|M4|^2` boundary exposed by #159. Do not read this mixed formula into #159's proved self-energy jet theorem.

## Falsification discipline

After the same-state theorem package is green, reuse existing R003 numerical/Arb backends to test the composed mechanism across:

- certified fixed cutoff cells;
- prime-power thresholds;
- small sizes and parity sectors;
- source-moment zero/near-zero cases;
- simultaneous both-parity badness;
- endpoint-scalar and `M4` degeneracies;
- modified-source controls.

Do not merely scan transformed total energy: retained transformed negativity is already theorem-backed.

## Dead shortcut remains dead

Exact boundary-flat K=2 fixtures still refute

```text
positive Riesz primitive + endpoint flatness
  -> pointwise fixed-sign smoothed integrand.
```

#159's integrated signed recurrence is not a revival of this pointwise route.

## Highest-leverage order

```text
FB-01  retained full first-bad certificate                         PROVED / #153
FB-02  exact finite pole-prime discrepancy                         PROVED / #153
FB-03A-D legal Riesz engine / parity-even jets                     PROVED / #155
FB-03E-F complex transport / retained transformed negativity       PROVED / #157
FB-04A exact moment jets + signed Riesz boundary recurrence         PROVED / #159
FB-04B same-state shifted Riesz x cross-parity source composition  OPEN / NEXT
FB-04C mixed source-pairing jet -> M4 bridge                       DERIVED / OPEN
FB-05  independent contradiction-producing arithmetic restriction  OPEN
FB-06  same-state contradiction / negative-root exclusion          OPEN
FB-07  terminal seam + Mathlib RH wrapper                          OPEN
```

## Permanent firewalls

- canonical sign-sensitive object remains `canonicalSourceMatrix`;
- theorem authority is through #159; machine-promoted claim IDs remain a separate, older surface;
- retained transformed negative energy is not a contradiction;
- exact Riesz identities are not arithmetic sign theorems;
- R8/R9 statements are conditional on even parity where stated;
- no factorwise division without theorem-backed nonzeroness;
- `D` is algebraic, not unitary/isometric;
- the mixed source-pairing jet is not yet theorem authority;
- interval-certified finite numerics are scoped falsification evidence only;
- negative-root exclusion still needs the outside-strip/trivial-zero seam;
- RH remains OPEN.

Detailed current implications:
`../../RESEARCH_LEADS_POST_159_RIESZ_CROSS_PARITY_FRONTIER_DELTA.md`.

**RH remains OPEN.**

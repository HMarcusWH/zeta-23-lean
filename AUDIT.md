# RHRC formal audit — theorem authority through PR #142; analytic regularity frontier

> **RH remains OPEN.**

## Current authority split

```text
live main after merged PR #142 = 3e8d2995a1c00a9aef0d8cb0f5382658c91a8673
live main tree = a92d03d0d4ad800d544a835b8ae2e3d23bae2c47

theorem-state anchor = PR #142 merge 3e8d2995a1c00a9aef0d8cb0f5382658c91a8673
validated theorem head = 23d96af9aafd86ad26ae7913c3d6c14503d539de
validated theorem tree = a92d03d0d4ad800d544a835b8ae2e3d23bae2c47
RHRC #889 = SUCCESS
Permansson #662 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
RH = OPEN
```

Live GitHub head + exact compiler/CI evidence outrank this prose.

## Exact theorem-state progression

### PR #134 — zero-shift source transport

**PROVED:** denominator-free whole-kernel source transport, direct zero-shift cross-parity transfer, exact zero-shift `Gamma` overlap formula, and `Gamma0*mu(z)=0` under both preimage hypotheses.

### PR #136 — absolute canonical source energy

**PROVED:** scalar-sensitive `matrixRealEnergy`, identity-shift sensitivity, exact prime/arch/scalar source-energy decomposition, cubic-shell energy, regular zero-shift trial energy `= Re S0`, and negative explicit Schur root -> negative canonical trial energy.

### PR #137 — canonical one-step determinant reduction

**PROVED:** exact complex source pairing, predecessor energy, shell coupling and

```text
Delta(w)=q_c*q_A(w)-|<w,b>|^2.
```

Also PROVED: conditional domination sufficiency, kernel/range zero-shift consequences, `Re S0>=0` under domination plus predecessor nonnegativity, no safe negative explicit Schur root under domination, exact domination-failure disjunction, and the global off-line-zero sign-failure countercertificate.

### PR #140 — aperture freedom and regularity scaffold

**PROVED:**

```text
off-line zero
  -> exists L0>0
  -> for every L>L0, a finite boundary-flat canonical negative witness exists.
```

Also PROVED:

```text
every sufficiently large L -> some AnyParityBad(L,N)
every sufficiently large L -> freshly selectable least global-first-bad Nstar
IntrinsicPredecessorRegular <-> injective intrinsicPredecessorBlock
regular predecessor -> unique cubic zero-shift preimage
floor(exp L)=Q -> frozenCanonicalPrimeMatrix Q L K = canonicalPrimeMatrix L K
L=log q -> entering source atom matrix is exactly zero
-2*wCorrection(L) = -log(L) + canonicalApertureScalarRemainder(L), L>0.
```

### PR #142 — fixed-cell canonical continuity and witness persistence

**PROVED:** on each physical cutoff cell `I_Q=(log Q,log(Q+1))` with `Q>=1`:

```text
floor(exp L)=Q;
entries of canonicalSourceMatrix are continuous;
fixed-vector real canonical quadratic energy is continuous;
a strict negative witness persists on an open in-cell neighborhood
with the same finite size N and the same vector u.
```

Exact headline declarations:

```text
continuousOn_canonicalSourceMatrix_apply_fixedCell
continuousOn_re_canonicalSourceQuadraticForm_fixedCell
exists_open_fixedCell_negativeCanonicalSourceWitness_persistence
eventually_fixedCell_negativeCanonicalSourceWitness_persists_of_offLine_zero
eventually_fixedCell_negativeCanonicalSourceWitness_persists_of_exists_offLine_zero
```

The final #142 RHRC run #889 and Permansson run #662 both succeeded on theorem head `23d96af9...`; the validated theorem tree equals merged-main tree `a92d03d0...`.

No theorem proves analytic continuation of the full frozen predecessor, determinant nonidentity, dense regular apertures, the final regular Schur sign, negative-root exclusion, or RH.

## Post-#142 research correction

#142 closes the continuity/persistence part of A4R. The preferred selection can now be simplified further.

**DERIVED:** choose the least bad size over an entire physical cutoff cell:

```text
K* = min { K | exists L in I_Q, AnyParityBad L K }.
```

Then every smaller size is good in both parities throughout that whole cell. At predecessor size `N*=K*-1`, both predecessor parity sectors are nonnegative for every aperture in the cell.

Take a negative parity witness at size `K*`. #142 preserves that same witness on an open `J subset I_Q`. If the relevant predecessor regularity set is dense, it meets `J`; at the selected point predecessor PSD + injectivity gives positive definiteness.

Therefore the primary route no longer needs:

```text
countable all-size Baire regularization;
finite-prefix simultaneous regularization through the witness size.
```

A standalone abstract conditional version of this cell-minimal selection has been locally Lean-checked, but it is not merged theorem authority and does not prove canonical determinant density.

## Active A4R1b theorem

The remaining regularization target is now:

```text
actual frozen intrinsic predecessor
  -> complex continuation of the exact production channels
  -> A(L) = -Log(L) I + B(L)
  -> single-valued holomorphic B on a connected punctured domain
  -> logarithmic monodromy + finite-dimensional spectrum
  -> determinant nonidentity
  -> dense regular apertures on I_Q.
```

The target must remain the actual `intrinsicPredecessorBlock`, not a proxy.

#142 makes direct analytic continuation more plausible because the real archimedean formulas already use origin-regularized divided slopes. After the real substitution `x=L t`, the integration interval becomes fixed. Those fixed-unit-interval formulas are **DERIVED**, not currently Lean declarations.

The candidate punctured domain must be proved channel by channel. A schematic strip bounded by the first nonzero imaginary hyperbolic singularities is a lead, not theorem authority.

## Candidate determinant nonidentity argument

The #140 scalar extraction supplies the real-axis logarithmic term. The desired lifted family is

```text
Ahat(z) = -z I + B(exp z)
```

with `B` single-valued in the aperture variable. Then

```text
B(exp(z+2*pi*i)) = B(exp z).
```

If `det Ahat` vanished identically, one fixed finite matrix would have arbitrarily many distinct eigenvalues differing by `2*pi*i`, impossible.

This is a **LEAD / HYPOTHESIS** until the full production continuation and exact operator decomposition are theoremized. The shortcut `A(exp z)=-zI+periodic` without proving the single-valued remainder remains forbidden.

## Stronger falsification after #142

A generic analytic centered diagonal family can satisfy all of:

```text
exact scalar -log L term;
positive predecessors throughout L>0;
persistent finite negative witnesses at every aperture;
a globally minimal bad size;
common negative behavior in both parities.
```

This is not the canonical zeta source. It proves only that aperture freedom, persistence, minimality, regularity, parity and scalar logarithms cannot themselves yield the final contradiction.

See `research/RHRC/countermodels/POST_142_REGULARIZATION_COUNTERMODEL_2026_09_10.md`.

Once both predecessors are regular, the #134 kernel product law becomes vacuous on the trivial kernel. Regularization removes resonance; it does not convert kernel transport into an energy sign theorem.

## Smallest remaining obstruction after successful analytic regularity

At the selected regular first-bad state:

```text
A>=0                    from cell/global first-bad minimality
A injective             from regularity
A>0                     finite Hermitian consequence
unique x0 with A x0=b   from #140 regularity scaffold
u0=c-x0.
```

The intended forced countercertificate is

```text
Ecanonical(u0)=Re S0<0.
```

The decisive arithmetic target remains

```text
Ecanonical(c-x0)>=0
```

on the exact forced production state, equivalently `<b,A^-1b><=q_c` once inverse shorthand is justified.

This is substantial new arithmetic. Universal one-step domination remains a valid broad closing condition but is not a reduced subproblem if its proof merely restates successor positivity.

## Current execution order

```text
1. production cell-minimal bad-state wrapper
2. complexify #142 regularized production primitives on an explicit common domain
3. build the exact frozen intrinsic predecessor and isolate -Log(L) I
4. prove finite-dimensional logarithmic-monodromy determinant nonidentity
5. derive dense fixed-cell regularity
6. intersect with #142 persistent negativity and package a regular first-bad certificate
7. expose the exact negative regular zero-shift source energy
8. derive an independent arithmetic contradiction from the full pole/arch/scalar/prime source
9. compose to negative-root exclusion
10. explicit Mathlib RiemannHypothesis wrapper
```

## Permanent firewalls

- compiler/CI validity is authoritative; repository presence alone is not;
- theorem authority is through #142 and no further;
- fixed-cell continuity/persistence is PROVED; analyticity/dense regularity is OPEN;
- cell-minimal regularization is DERIVED until merged;
- regularity is not positivity of the successor;
- all-size Baire and finite-prefix regularization are fallback infrastructure, not current dependencies;
- universal determinant positivity cannot count as a reduction if it merely restates successor PSD;
- no `A^-1` at zero before regularity; formal code should prefer the unique-preimage interface;
- `Gamma0*mu(z)=0` with trivial kernel is not a sign theorem;
- D is algebraic, not unitary/isometric;
- no division by unproved transfer/source factors;
- modified-source or generic countermodels are not zeta counterexamples;
- numerical precision is not theorem authority;
- machine claim promotion remains separate;
- RH remains OPEN.

Newest research implications: `research/RHRC/RESEARCH_LEADS_POST_142_FIXED_CELL_PERSISTENCE_DELTA.md`.

**RH remains OPEN.**
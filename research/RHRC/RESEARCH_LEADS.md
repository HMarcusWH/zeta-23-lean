# RHRC living research leads ledger

> **Claim firewall: RH remains OPEN.**
>
> This is a research inventory, not theorem authority. Exact Lean/compiler/CI state wins.

## Current theorem / research authority

```text
live main after merged PR #161 = ef29b45de683962122c1e898ed31bf9417757125
live main tree = b080572e87068889a72b4e612f99ddf0bd67f482
latest theorem-bearing PR = #161
validated theorem head = 188407fb02a37de2e380ede3b60e140953b01441
validated theorem tree = b080572e87068889a72b4e612f99ddf0bd67f482
RHRC #1026 = SUCCESS
Permansson #799 = SUCCESS
newest post-green delta = RESEARCH_LEADS_POST_161_SAME_STATE_RIESZ_SOURCE_RIGIDITY_DELTA.md
current execution SSOT = CURRENT_RESEARCH_PLAN.md
RH = OPEN
```

## Promoted theorem inputs

### Retained first-bad state — PROVED / #153

`RegularCellMinimalFirstBadCertificate` and `RegularCellMinimalNegativeEnergyCertificate` retain whole-cell ancestry, selected regular predecessor, negative explicit root, exact `A x0=b`, and negative canonical energy.

### Exact discrepancy + legal Riesz engine — PROVED / #153/#155

Pole/prime cancellation is theoremized before smoothing. Left-anchored Riesz primitives, absolute continuity, a.e. derivative recovery and arbitrary-order conditional integration by parts are compiler-validated.

### Complex production transport + transformed negativity — PROVED / #157

Complex production D-transport, boundary-flat jets through 6, even jets through 8, exact complete Riesz 6/even 8, retained transformed negativity and the ExceptionalZero Riesz-6 wrapper are theorem authority.

### Exact moment-prefix jets + signed Riesz boundary — PROVED / #159

The general moment-prefix odd-jet theorem, exact seventh/even-ninth self-energy leading-moment formulas, generic signed Riesz recurrence and retained R6->R7 / even R8->R9 boundary decompositions are theorem authority.

### Same-state shifted Riesz x cross-parity source — PROVED / #161

#161 adds:

```text
parityBad_of_negative_eigenmode
predecessorNonnegative_anyParity
negative shifted secular-root canonical/source energy
even shifted Riesz-8 negativity
exact shifted Riesz-9 / M4 boundary inequality
opposite secular nonroot under opposite-parity goodness
odd scalar = Gamma * explicitCanonicalSourceMoment on retained even shifted trial
odd-good -> explicit source moment != 0
odd-bad OR explicit-source-moment-nonzero retained fork
```

The same canonical shifted negative state now carries spectral, local-moment and global-arithmetic constraints.

## Active lead — mixed source-pairing jet / M4 rigidity

**Research status:** ACTIVE / HIGHEST LEVERAGE  
**Formal status:** DERIVED / OPEN IN LEAN

For the quadratic-normal source pairing

```text
h_v(omega) = <n2, sourceMatrix(omega) v> / <n2,n2>
```

the post-green calculation predicts, for even boundary-flat `v`,

```text
h_v^(7)(0) = -2*(2*pi)^6 * M4(v).
```

If theoremized, this connects the linear quadratic-normal source jet to the theorem-backed quadratic #159/#161 Riesz boundary proportional to `|M4(v)|^2`.

The useful target is not just the derivative identity. It is whether the retained shifted secular state satisfies an additional canonical relation between this local mixed jet and

```text
explicitCanonicalSourceMoment L (N+1) evenShiftedTrial.
```

Do not confuse the mixed-pairing formula with #159's already-proved self-energy ninth derivative.

## Active lead — source moment / M4 separation falsification

**Research status:** TEST BEFORE STRONG RIGIDITY THEOREM  
**Formal status:** OPEN

Retarget theorem-aligned exact/Arb tooling to the same shifted state and ask whether one can realize:

```text
explicitCanonicalSourceMoment != 0 with M4 = 0
M4 != 0 with explicitCanonicalSourceMoment = 0.
```

The generic vector-space answer may be yes. The relevant question is whether the **canonical shifted secular state** imposes an extra relation.

Repeated finite success is not a theorem.

## Active lead — simultaneous parity badness

**Research status:** FALSIFY BEFORE LEAN INVESTMENT  
**Formal status:** OPEN

#161's left branch permits simultaneous even and odd badness at the same successor size over a globally good predecessor scale.

Use exact rational/generic rank-one parity models to test whether such simultaneous badness is structurally easy. If yes, no generic rank-one/parity argument can close this branch; exact arithmetic must enter.

## Coverage lead — odd-selected first bad

**Research status:** OPEN COVERAGE DEBT

#161's retained same-state theorem is conditional on selected parity being even. There is no WLOG-even theorem because `D` is algebraic rather than unitary/isometric and the two parity compressions are not spectrally identified.

Possible future routes are reverse cross-parity transfer, an odd analogue of the mixed rigidity theorem, or a separate argument excluding odd-selected first badness.

## Derived lead — Gamma nonzero under odd-good

**Formal status:** DERIVED

Under even-selected + odd-good, #161 proves

```text
F_odd(lambda) != 0
F_odd(lambda) = Gamma(lambda) * explicitCanonicalSourceMoment(...).
```

Therefore both factors are nonzero, without division. Theoremize this only if it simplifies later composition.

## Decisive lead — independent contradiction-producing arithmetic restriction

**Formal status:** OPEN

The terminal arithmetic task remains a genuinely independent canonical restriction on the exact forced state. It may be a relation between global source moment and local mixed jet/Riesz boundary, a simultaneous-parity incompatibility that genuinely spends canonical arithmetic, a nonnegative transformed residual, or another theorem that excludes the retained negative root without restating successor positivity.

## Dead route — pointwise positivity after smoothing

The exact boundary-flat K=2 fixtures still refute

```text
positive Riesz primitive + endpoint flatness
  -> pointwise fixed-sign smoothed integrand.
```

#159 proves an integrated signed boundary recurrence and #161 proves same-state composition. Neither revives this dead pointwise claim.

## Broad fallback — universal one-step domination

`canonicalOneStepDomination` remains theorem-backed as a sufficient certificate but is research-useful only if an independent canonical arithmetic mechanism proves it. A proof that merely repackages successor positivity is circular for discovery purposes.

## Quarantines

- generic Hermitian/parity/KKT/displacement structure without exact source arithmetic;
- factorwise division by `alpha`, `Gamma`, overlap or source moment;
- `D` treated as unitary/isometric;
- atomwise positive determinant/SOS;
- independent coarse pole/prime/arch/scalar majorants;
- global aperture or Schur monotonicity as a substitute for root exclusion;
- treating the mixed source-pairing jet as already proved;
- inferring `M4 != 0` from nonzero explicit source moment or conversely;
- treating retained/shifted R8/R9 as parity-unconditional;
- assuming the selected parity is even WLOG.

## Standing research questions

1. Can the mixed quadratic-normal source pairing be theoremized with exact production conjugation and normalization?
2. Does its seventh jet equal `-2*(2*pi)^6*M4` on every even boundary-flat carrier?
3. On the canonical shifted secular state, is the global explicit source moment constrained by that local `M4` jet in a way generic vectors are not?
4. Is simultaneous even+odd badness generic, or does canonical arithmetic restrict it?
5. What closes the odd-selected branch?
6. Does any proposed closing lemma secretly assume successor positivity or RH-strength content?

**Current highest-information question:** does the canonical shifted negative eigenstate satisfy a non-generic arithmetic rigidity relation linking the #161 global source obstruction to the #159/#161 local `M4` Riesz boundary?

**RH remains OPEN.**

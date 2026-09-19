# Post-#221 zero-shift Schur classification research delta

> **Claim firewall: RH remains OPEN.**
>
> Merged theorem authority remains PR #220. The exact PR #221 theorem delta at
> `20018c931f4516432ace5bd06788276be656641b`, tree
> `bc82b7604d95ccce8f1a46e4b25e0485bf68a4c2`, passed the CCM build,
> exceptional-zero build, and forbidden-placeholder gate before this
> documentation synchronization. PR #221 is not yet merged in this snapshot.

# What became formally true

The validated theorem delta proves, under `0 < L`, `1 <= N`, and predecessor
nonnegativity:

```text
ParityBad p L (N+1)
iff
  cubicCouplingKernelPart p L N != 0
  or
  exists x0,
    intrinsicPredecessorBlock p L N x0
      = intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N)
    and re(cubicZeroShiftSchurEndpoint p L N x0) < 0.
```

It also proves the complementary exact classification:

```text
not ParityBad p L (N+1)
iff
  exists x0,
    A x0 = b
    and 0 <= re S0(x0).
```

The headline generic declarations are
`parityBad_iff_cubicCouplingKernelPart_ne_zero_or_exists_zeroShiftEndpoint_neg`
and
`not_parityBad_iff_exists_cubicZeroShiftPreimage_endpoint_nonnegative`.
The retained route-facing declaration
`RegularCellMinimalNegativeEnergyCertificate.oddBad_iff_oddCubicCouplingResonant_or_zeroShiftEndpoint_neg`
specializes the exact split to the retained first-bad state.

# What changed

Before #221, simultaneous odd badness was an opaque open branch. #220 proved
that odd goodness kills the actual shell-coupling kernel coordinate and
supplies an odd zero-shift preimage, but did not characterize odd badness.

The validated #221 delta turns successor badness into an exhaustive structural
fork:

```text
RESONANT:
  K_-(b_-) != 0

REGULAR-NEGATIVE:
  K_-(b_-) = 0,
  A_- x_- = b_-,
  re S0,-(x_-) < 0.
```

Here `K_-(b_-)` is the kernel coordinate of the **actual shell coupling**.
It is not #219's `K_-(a)` and not #220's transported correction
`K_-(d)`.

# Upstream implications

Good-sector zero-shift solvability is no longer an auxiliary hypothesis:
`not ParityBad` is equivalent to regular zero-shift solvability together with
a nonnegative endpoint. The zero-shift range/kernel machinery can therefore be
used through this canonical good/bad interface rather than carrying redundant
preimage hypotheses on good sectors.

The classification also isolates the minimum reusable abstraction beneath the
older one-step-domination route. Full determinant domination is not needed to
classify the geometry; the actual kernel coordinate plus endpoint sign are the
canonical branch variables.

# Downstream implications

On the retained even-selected / odd-good branch the project now has, at once:

```text
re sigma_+ < 0
odd-good -> exists x_- with re S0,- >= 0
sigma_+ K_-(d) + mu_0 K_-(a) = 0
#219 regular/resonant dichotomy for K_-(a)
```

The simultaneous odd-bad branch is not closed, but it is now reduced to the
two explicit Schur mechanisms above. This gives a finite branch inventory for
the next arithmetic discrimination pass.

# Resurrected routes

The zero-shift cross-parity response route is now fully branch-aware. On the
odd-good branch an odd preimage is theorem-generated; on the odd-bad branch
#221 says exactly whether failure is resonant or regular-negative.

The resonant pole route is also sharpened conceptually: one must distinguish
resonance of the actual shell coupling `K_-(b_-)` from the independent #219
source-correction resonance `K_-(a)`. A successful next theorem may relate
these coordinates, but they must not be conflated.

# New RH-relevant clues

**LEAD / HYPOTHESIS.** The admissible first-bad state is increasingly described
by a small set of discrete Schur geometries plus exact arithmetic balance laws.
A decisive route may come from proving that canonical arithmetic cannot satisfy
one or more of these branch combinations, rather than from a universal
positivity theorem.

**DERIVED.** The odd-good branch has opposite zero-shift sign information:
the selected even response is strictly negative while the odd-good zero-shift
endpoint is nonnegative. Combined with the existing direct scalar transfer and
#220 kernel balance, this gives two same-state compatibility equations to test
against canonical arithmetic.

# Falsification checks

1. `K_-(d)` may vanish generically because the odd predecessor block is
   invertible; then the #220 kernel balance has limited branch-selection power.
2. The resonant actual-shell branch `K_-(b_-)
e0` may coexist harmlessly with
   the #219 source-correction branch because the two kernel vectors are distinct.
3. The regular-negative endpoint branch may occur in generic Hermitian block
   systems, so its exclusion must spend canonical arithmetic rather than pure
   Schur algebra.
4. No contact-state substitution is authorized; the retained certificate is
   still a negative secular root.

# Highest-leverage next moves

The next descriptive target is
`RETAINED_BRANCH_ARITHMETIC_DISCRIMINATION`:

1. theoremize the exact kernel/range resolvent cost for the #219 correction
   `a`, separating pole and regular costs;
2. theoremize the same-state zero-shift/negative-shift observable bridge;
3. run a frozen bounded falsification audit of predecessor rank/kernel geometry,
   especially whether `K_-(d)` or actual-shell resonance can be nontrivial on
   inherited canonical states;
4. only after that evidence, attempt branch-exclusion theorems.

The odd-selected branch, negative-root exclusion, finite obstruction exclusion,
finite-to-zeta closure, and RH remain OPEN.

# Standing questions

Given the now-exact good/bad Schur classification, what arithmetic fact
distinguishes the resonant and regular-negative branches in the canonical
matrix family?

Can the #219 source-correction kernel coordinate, #220 transported-index
kernel coordinate, and #221 actual-shell kernel coordinate be related by a new
canonical identity without collapsing them into the same object?

What is the cheapest theorem or frozen audit that can falsify such a relation
before another large proof investment?

**RH remains OPEN.**

# RHRC formal audit — theorem authority through PR #134; energy frontier synchronized

> **RH remains OPEN.**

## Current authority split

```text
live main after theorem PR #134 = 7f1fec480d1ccbff04a456ab937accf7b23cc1af
live main tree = c142efa141036331d139c532d06e7a976c5b50c2

theorem-state anchor = PR #134 merge 7f1fec480d1ccbff04a456ab937accf7b23cc1af
validated theorem head = 753ee53a7fc08bd3be9a5a0f37417629122395f9
validated theorem tree = c142efa141036331d139c532d06e7a976c5b50c2
theorem-bearing merged through = PR #134
RHRC #870 = SUCCESS
Permansson #643 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12

RH = OPEN
```

Live GitHub head + exact compiler/CI evidence outrank this prose. PR #134 changed Lean theorem state and therefore supersedes #131 as the theorem anchor. Machine claim promotion remains a separate surface.

## Theorem history relevant to the active route

### PR #112/#113 — global first-bad block geometry

**PROVED:** global first badness; both predecessor parities nonnegative below the first bad size; intrinsic predecessor `W`; one-step shell `S` with complex finrank one; negative first-bad eigenmode with nonzero shell content; canonical `V=W⊕S`; projected predecessor block `A=P_WT|_W`; safe shifted inverse for `lam<0`; basis-free shifted Schur identity.

### PR #115/#118/#119/#121/#122 — cubic coordinates, secular theorem and metric control

**PROVED:** canonical cubic shell/quotient coordinates; exact negative secular root iff eigenmode; exact explicit Schur scalar bridge; projected predecessor symmetry; shifted coercivity and resolvent metric control; zero-resonance coupling classification.

### PR #124/#125/#127/#128 — zero-shift geometry

**PROVED:** `W=ker A⊕range A`; canonical zero-shift preimage/endpoint when the coupling annihilates the kernel; `Re S0<0` at the forced negative root; exact shell response `sigma0*c=T u0`; regular `Re sigma0<0`; canonical resonant kernel coordinate and exact `1/(-lam)` pole.

None of these statements alone is branch exclusion.

### PR #129 — source-explicit cross-parity transport

**PROVED:**

```text
F_- = alpha * F_+ + Gamma * sourceMoment(u_+)
```

with the cubic defect coefficient identified with the actual canonical quadratic source moment. The predecessor correction in `D c+` is retained and D is not upgraded to unitary/isometric. A hypothetical off-line zero is attached to the same global-first-bad source-explicit finite certificate.

### PR #131 — exact production source-moment decomposition

**PROVED:**

```text
canonicalSourceMatrix
  = canonicalPoleMatrix
    - canonicalArchMatrix
    - canonicalPrimeMatrix
```

with the archimedean scalar identity separated, reduced arch diagonal/off-diagonal split, finite von-Mangoldt prime atomization, pole even/odd factorization, odd-profile cancellation on even boundary-flat inputs, and

```text
cubicDefectFunctional L K v
  = explicitCanonicalSourceMoment L K v.
```

The active quadratic-normal moment annihilates the scalar identity term by design.

### PR #134 — exact denominator-free kernel/source transport and direct zero-shift transfer

Exact theorem head: `753ee53a7fc08bd3be9a5a0f37417629122395f9`.  
Merged theorem state: `7f1fec480d1ccbff04a456ab937accf7b23cc1af`.  
Validated theorem tree: `c142efa141036331d139c532d06e7a976c5b50c2`.

Exact-head workflows:

```text
RHRC #870 = SUCCESS
Permansson #643 = SUCCESS
```

**PROVED — kernel transport.** For every `z in ker A+`:

```text
A-(Dz) = beta(z)d + mu(z)a
<b-,Dz>/rho- = beta(z)+mu(z)
```

where `mu` is the #131 production source functional.

**PROVED — whole odd-kernel compatibility.** Projecting gives the vector identity

```text
beta(z) K-d + mu(z) K-a = 0
```

in the entire odd predecessor kernel. The canonical even cubic-coupling kernel component receives the exact self-inner coefficient specialization.

**PROVED — even-regular odd-kernel response.** If the even cubic coupling has a zero-shift preimage, the odd cubic coupling-kernel component is exactly the sum of the even zero-shift response direction and the exact source direction.

**PROVED — direct zero-shift cross-parity transfer.** If both parity couplings have explicit preimages:

```text
sigma- = alpha0 sigma+ + Gamma0 * mu(u+0)
Gamma0 = <u-0,g->/rho-.
```

This is proved at zero itself; no pseudoinverse, Laurent expansion, resolvent limit or whole-block inverse is used.

**PROVED — regular-kernel product law.** Under both preimage hypotheses:

```text
Gamma0 * mu(z) = 0
```

for every `z in ker A+`.

**Not proved:** `Gamma0!=0`; `mu(z)=0` separately; source sign; canonical energy positivity; branch exclusion; negative-root exclusion; RH.

## What #134 changes mathematically

The zero-shift transport problem is no longer an open algebraic bottleneck. The project has a direct finite theorem at zero that is stronger than the scalar cancellation one would obtain from a Laurent expansion.

The regular preimage equation also forces `beta(z)=0` for every even predecessor-kernel vector by symmetry. Hence the regular-branch kernel transport becomes source-driven rather than mixed with the shell-coupling coefficient.

The product law `Gamma0*mu(z)=0` is a genuine whole-kernel restriction, but exact countermodels already warn that neither factor can be assumed nonzero structurally. Therefore #134 does not justify division by either factor.

## Current formal state

```text
off-line zero -> finite global first-bad state                          PROVED
negative exact secular/eigenvalue root                                  PROVED
both predecessor parities nonnegative                                   PROVED
zero-shift kernel/range package                                          PROVED
Re S0<0 at forced negative root                                          PROVED
special zero-shift shell response                                        PROVED
regular Re sigma0<0                                                      PROVED
canonical resonant kernel pole                                           PROVED
source-explicit cross-parity transfer                                    PROVED
exact canonical source-moment decomposition                              PROVED / #131
whole-kernel denominator-free source transport                           PROVED / #134
direct zero-shift cross-parity transfer                                  PROVED / #134
Gamma0*mu(z)=0 on full even predecessor kernel                           PROVED / #134

absolute canonical source-energy decomposition                           OPEN / NEXT THEOREM
canonical one-step domination/coercivity                                 OPEN / DECISIVE TARGET
regular-aperture log-lift selection                                      LEAD / OPTIONAL
negative-root exclusion                                                   OPEN
explicit terminal RH bridge                                               OPEN
RH                                                                        OPEN
```

## Current research frontier

### E4-A4b1 — absolute canonical source energy

Lift the production source decomposition from the shift-invariant #131 moment to

```text
E(v)=Re<Tv,v>
```

while retaining the canonical archimedean scalar identity correction. The next theorem package should expose the exact pole / reduced-arch-diagonal / reduced-arch-off-diagonal / scalar-correction / finite-prime energy decomposition and specialize it to the cubic shell and zero-shift trial.

The immediate goal is exact bookkeeping plus the regular-preimage energy/Schur identity. Positivity must not be smuggled into the decomposition theorem.

### E4-A4b2 — canonical one-step domination

For either parity, with `A>=0`, shell `c`, coupling `b=P_WTc`, and `q_c=Re<Tc,c>`, prove from the actual canonical source

```text
q_c >= 0
|<w,b>|^2 <= q_c Re<Aw,w>  for every w in W.
```

If proved, kernel vectors annihilate the coupling and a regular solution gives `S0>=0`, contradicting the existing `Re S0<0` at the forced negative root.

This is the central unresolved finite arithmetic/coercive theorem.

### E4-A4R — optional regular-aperture log-lift

Frozen-cutoff analyticity and the `-log(L)I + periodic remainder` structure may produce dense injective predecessor apertures. This can simplify resonance but cannot by itself exclude a negative successor.

## Falsification state

Exact rational generic centered-grid countermodels preserve the legal parity/boundary-flat/KKT/rank-one/transfer structure while realizing `Gamma=0`, `alpha=0`, source-moment zero/nonzero and both source-moment signs at negative-root configurations. They are not canonical arithmetic sources and not RH counterexamples.

The simultaneous generic scalar shift

```text
M -> M+tI
lambda -> lambda+t
```

can preserve the transfer package while moving the spectrum across zero. Therefore any final sign proof must visibly spend canonical normalization information that is not shift-invariant.

Boundary-flat Taylor algebra predicting `omega^7` / `omega^9` leading source-coordinate orders remains **DERIVED / EXPERIMENTAL** until theoremized.

## Permanent firewalls

- compiler/CI validity is authoritative; repository presence alone is not;
- supporting theorem checks do not automatically imply machine claim promotion;
- `V=W⊕S` does not imply shell invariance;
- D is algebraic, not unitary/isometric;
- the D-transport predecessor correction may not be dropped;
- `ker A` is not the predecessor-size compressed-operator kernel;
- no `A^-1` at zero;
- `Re S0<0` and `Re sigma0<0` are not branch exclusion;
- the resonant pole is classification, not contradiction;
- `Gamma0*mu(z)=0` is a product law, not factorwise exclusion;
- no division by `alpha`, `Gamma`, overlap or source moment without theoremized nonzeroness;
- universal raw source-moment positivity is unavailable for the linear observable;
- factorwise sign/nonzero closure is quarantined by exact rational countermodels;
- shift-invariant transfer data cannot locate the absolute spectral origin;
- positive-definite predecessors are simplification, not exclusion;
- generic countermodels do not refute the canonical arithmetic source;
- numerical precision is not theorem authority;
- root uniqueness remains weaker than root exclusion;
- no negative-root exclusion or RH change is implied by the current theorem state.

Detailed current research implications: `research/RHRC/RESEARCH_LEADS_POST_134_DELTA.md`.

**RH remains OPEN.**

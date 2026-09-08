# RHRC formal audit — theorem authority through PR #131; post-#132 research frontier synchronized

> **RH remains OPEN.**

## Current authority split

```text
live main after documentation PR #132 = 38f65ce4abf5eec258d51425e7c9c88b63b21ffb
live main tree = 1cc939300fb269f798d25dc88f8eaff4eccc181a

theorem-state anchor = PR #131 merge 436d524d0cdeb5986d76dcbb988f771d19836c55
validated theorem head = b0026683bcbf233afa947c7f15b57bcc4ddf31e3
validated theorem tree = 5ad51fd877d51348f1af474b2864eb4ab3e0617a
theorem-bearing merged through = PR #131
RHRC #854 = SUCCESS
Permansson #627 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12
control-plane tree = c0d28740806ec22b5b477b426a2a31e459672dd1

RH = OPEN
```

Live GitHub head + exact compiler/CI evidence outrank this prose. PR #132 changed documentation/control metadata only and passed the repository checks at its exact head before merge; it did not add a Lean theorem. The exact #131 theorem head remains mathematical authority.

## Theorem history relevant to the current route

### PR #112/#113 — global first-bad block geometry

**PROVED:** global first badness; both predecessor parities nonnegative below the first bad size; intrinsic predecessor `W`; one-step shell `S` with complex finrank one; first-bad negative eigenmode with nonzero shell content; exact cubic parity-defect factorization; canonical `V=W⊕S`; projected predecessor block `A=P_WT|_W`; safe shifted inverse for `lam<0`; basis-free shifted Schur identity.

### PR #115/#118 — canonical cubic shell and quotient coordinates

**PROVED:** canonical cubic successor direction is not inherited from the predecessor; nonzero shell part; exact shell reconstruction; faithful quotient coordinate; normalized negative eigenmode; odd cubic parity-defect coefficient identified with the canonical quotient coordinate of the exact intertwining defect.

### PR #119/#121/#122 — exact secular theorem and metric control

**PROVED:** for safe `lam<0`,

```text
cubicSecularScalar(lam)=0
  <-> full residual=0
  <-> canonical trial vector is a genuine eigenmode
  <-> exists nonzero eigenmode at lam.
```

The quotient scalar is exactly bridged to the explicit Schur scalar; the explicit scalar is real on the safe negative axis; projected predecessor symmetry, shifted coercivity and resolvent metric control are theorem-backed. `ker A` zero-resonance coupling is classified but not excluded.

### PR #124/#125 — zero-shift geometry and negative endpoint

**PROVED:**

```text
W = ker A ⊕ range A
```

with orthogonality and zero intersection. If the coupling annihilates `ker A`, a zero-shift preimage `Ax0=b` exists and the canonical endpoint

```text
S0=<Tc,c>-<x0,b>
u0=-x0+c
```

is solution-independent. At the forced negative root:

```text
Re S0 < 0.
```

This is not branch exclusion.

### PR #127 — special zero-shift shell response

**PROVED:** for the decoupled zero-shift trial,

```text
T u0 = shellPart(T u0)
sigma0*c = T u0
S0 = star(sigma0)<c,c>.
```

This does not make the shell invariant and does not make `u0` an eigenvector.

### PR #128 — regular response and resonant kernel pole

**PROVED:** in the regular branch at the forced negative root,

```text
Re sigma0 < 0.
```

The canonical predecessor-kernel coordinate `K` gives

```text
(-lam) K(R_lam b) = K(b).
```

The decoupled branch has `k=K(b)=0`; the resonant branch has `k!=0` and the exact divided `1/(-lam)` pole for `lam<0`. Neither branch is excluded.

### PR #129 — source-explicit cross-parity transport

**PROVED:** the cubic parity-defect coefficient is exactly the actual canonical quadratic source moment and

```text
F_- = alpha * F_+ + Gamma * sourceMoment(u_+).
```

The predecessor correction in `D c+` is retained. D is never upgraded to unitary/isometric.

**PROVED:** a hypothetical off-line zero is forced to one global-first-bad finite state carrying the same source-explicit cross-parity certificate at the same negative explicit root.

### PR #131 — exact production source-moment decomposition

Exact theorem head: `b0026683bcbf233afa947c7f15b57bcc4ddf31e3`.  
Merged theorem state: `436d524d0cdeb5986d76dcbb988f771d19836c55`.  
Validated theorem tree: `5ad51fd877d51348f1af474b2864eb4ab3e0617a`.

**PROVED:**

```text
canonicalSourceMatrix
  = canonicalPoleMatrix
    - canonicalArchMatrix
    - canonicalPrimeMatrix
```

with the canonical arch scalar separated as a scalar identity, reduced arch diagonal/off-diagonal split, finite von-Mangoldt prime atomization, exact pole even/odd factorization, odd-profile cancellation on even boundary-flat inputs, and

```text
cubicDefectFunctional L K v
  = explicitCanonicalSourceMoment L K v.
```

The active moment equals

```text
poleEven
- reducedArchDiagonal
- reducedArchOffDiagonal
- finitePrimeAtomSum.
```

**Not proved:** sign/nonzeroness of the explicit source moment, overlap, `Gamma`, or `alpha`; branch exclusion; negative-root exclusion; RH.

### PR #132 — documentation/control synchronization

**DOCUMENTATION/CONTROL ONLY.** No `.lean` theorem authority was added. Theorem authority remains #131. The merged main commit after #132 is `38f65ce4abf5eec258d51425e7c9c88b63b21ffb`.

## Post-#132 research audit — labels matter

### DERIVED — denominator-free kernel/source transport target

For `z in ker A+`, the existing #129/#131 parity-defect and quotient identities imply the target

```text
A-(Dz) = beta(z) d + mu(z) a
<b-,Dz>/rho- = beta(z) + mu(z)
```

with `beta(z)=<b+,z>/rho+`. Projecting to the full odd predecessor kernel yields

```text
(||K+b+||^2/rho+) K-d + mu(K+b+) K-a = 0.
```

This is a derived algebraic consequence, not yet a compiled Lean theorem.

### DERIVED — direct zero-shift transfer

Assuming only predecessor preimages `A+ x+=b+` and `A- x-=b-`, the exact target is

```text
sigma- = alpha0 sigma+ + Gamma0 mu(u+0)
Gamma0 = <u-0,g->/rho-.
```

No pseudoinverse, Laurent limit, positive definiteness, or whole-block inverse is required. The endpoint response is preimage-independent; `alpha0` and `Gamma0` individually need not be.

### DERIVED — regular-kernel overlap/source annihilation

Under both regular couplings,

```text
Gamma0 * mu(z) = 0
```

for every `z in ker A+`. This is a conditional compatibility law, not branch exclusion.

### EXPERIMENTAL SIGNAL — exact rational generic countermodels

Exact centered-grid reversal-symmetric diagonal fixtures preserve the legal parity/boundary-flat spaces, predecessor nonnegativity, KKT geometry, rank-one cubic defect, quotient transport, trial reconstruction, overlap formula and full #129 scalar transfer while realizing:

```text
sourceMoment(u+) != 0 with Gamma = 0 at a common negative root
Gamma != 0 with sourceMoment(u+) = 0 at a common negative root
alpha = 0 at an odd-only negative root with positive even successor
```

Additional fixtures realize negative `Gamma`, negative `alpha`, and either sign of the source moment. These are not canonical arithmetic CCM sources and not RH counterexamples.

### DERIVED FIREWALL — scalar-shift origin blindness

In the generic structural package, the simultaneous shift

```text
M -> M+tI
lambda -> lambda+t
```

can preserve the trial vectors, source/defect functional, `alpha`, `Gamma`, and secular transfer data while moving the spectrum relative to zero. Therefore the shift-invariant structural transfer package cannot by itself decide negative versus positive absolute spectrum.

This makes the missing information channel explicit: canonical absolute normalization.

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

kernel/source zero-shift transport                                       DERIVED / NOT YET LEAN
absolute canonical source-energy decomposition                           OPEN
canonical one-step domination/coercivity                                 OPEN / DECISIVE TARGET
regular-aperture log-lift selection                                      LEAD / OPTIONAL
negative-root exclusion                                                   OPEN
explicit terminal RH bridge                                               OPEN
RH                                                                        OPEN
```

## Current research frontier

### E4-A4b0 — kernel/source transport

Formalize the denominator-free kernel vector identity, its full-kernel projection, direct zero-shift transfer, and the regular-kernel `Gamma0*mu(z)=0` compatibility theorem. Do not add pseudoinverse or Laurent machinery merely to recover a weaker scalar cancellation.

### E4-A4b1 — absolute canonical source energy

Lift the #131 production channel decomposition from the shift-invariant quadratic-normal moment to

```text
Re<Tv,v>
```

while retaining the canonical archimedean scalar correction. This is the source quantity that remembers the absolute spectral origin.

### E4-A4b2 — canonical one-step domination

For either parity, with `A>=0`, shell `c`, coupling `b=P_WTc`, and `q_c=Re<Tc,c>`, prove from the actual canonical source

```text
q_c >= 0
|<w,b>|^2 <= q_c Re<Aw,w>  for every w in W.
```

If proved, kernel vectors force the coupling into `range A`, removing resonance, while a regular solution `Ax0=b` gives `S0>=0`, contradicting the existing `Re S0<0` at the forced negative root.

This is the central unresolved arithmetic/coercive theorem.

### E4-A4R — log-lift regular-aperture selection

Optional simplifier if resonance materially complicates the arithmetic estimate. Frozen-cutoff analyticity plus

```text
M_Q(L)=-log(L)I+B_Q(L),  L=exp(z)
```

and periodic determinant nonidentity may yield dense apertures with injective predecessor parity blocks. Preserve a negative witness by continuity and reselect the least-bad size. This does not itself exclude a negative successor.

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
- no division by `alpha`, `Gamma`, overlap or source moment without theoremized nonzeroness;
- universal raw source-moment positivity is dead by linearity;
- factorwise sign/nonzero closure is quarantined by exact rational countermodels;
- shift-invariant transfer data cannot locate the absolute spectral origin;
- positive-definite predecessors are simplification, not exclusion;
- generic countermodels do not refute the canonical arithmetic source;
- numerical precision is not theorem authority;
- root uniqueness remains weaker than root exclusion;
- no negative-root exclusion or RH change is implied by the current documentation/research audit.

Detailed current research implications: `research/RHRC/RESEARCH_LEADS_POST_132_DELTA.md`.

**RH remains OPEN.**

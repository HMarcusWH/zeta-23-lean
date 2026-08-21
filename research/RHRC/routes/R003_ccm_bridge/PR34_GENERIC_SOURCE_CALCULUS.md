# PR #34 — generic divided-difference / source calculus

Status: **exact-head green; ready to merge; no RHRC claim promotion**.

This PR implements the first theorem layer after PR #33's normalization lock. Its purpose is to separate the universal finite divided-difference chassis from the zeta-specific channel formulas before the finite Guinand--Weil dictionary is formalized.

## Scope

Lean modules:

```text
Zeta23/CCM/DividedDifference.lean
Zeta23/CCM/SourceMatrix.lean
```

The existing `Zeta23/CCM/Displacement.lean` is refactored so the public concrete CCM theorems remain available, but the centered matrix commutator/rank proof is inherited from the generic class after the zeta-specific scalar entry is identified with it.

## Generic chassis

For source values `psi : Z -> C` and independently supplied diagonal data `d : Z -> C`, define

```text
Q_psi,d(n,m) = d(n)                         if n = m
             = (psi(n)-psi(m))/(n-m)        if n != m.
```

The diagonal is deliberately independent of `psi`: the displacement calculation does not use it.

Proved theorems:

```text
(n-m) Q_psi,d(n,m) = psi(n)-psi(m)
[D,Q_psi,d] = psi 1^T - 1 psi^T
rank([D,Q_psi,d]) <= 2
[D,Q_psi,d1] = [D,Q_psi,d2].
```

This formally records that low displacement rank is a divided-difference/Loewner class property. `R004_CCM_DISPLACEMENT_FORMAL` remains a proved unconditional theorem, but its rank-two conclusion is not treated as an RH-specific discriminator.

## Elementary single-frequency source

For real source coordinate `omega`, define

```text
psi_omega(n) = sin(2*pi*n*omega)/pi
d_omega(n)   = 2*omega*cos(2*pi*n*omega).
```

The resulting centered matrix is a specialization of the generic class. The sign/parameter acceptance theorem for the next dictionary PR is proved exactly:

```text
sourceEntry(1-y/L,n,m) = qBasis(n,m,y,L).
```

This is a compiler-checked convention bridge, not a numerical convention check.

## Concrete CCM specialization

The existing channel lemmas remain the zeta-specific input:

```text
poleComponent_displacement
archComponent_displacement
primeComponent_displacement
entry_displacement.
```

They identify the concrete source potential

```text
g_n = poleSeq(n,L) + alphaL(n,L) + primeSeq(n,L)
```

and prove that the formal CCM scalar entry is an instance of `Q_psi,d`, with `d(n)=entry(n,n,L)`. The finite CCM displacement and rank theorems are then specialized from the generic matrix theorem.

## Deliberate non-scope

This PR does **not** prove or promote:

- the `2N+1` source quotient;
- the coefficient-vector chain `v -> T_v -> K_v -> ghat_v -> g_v`;
- explicit-formula admissibility;
- a zero-side sum identity;
- the formal `Q_inf` normalization bridge;
- positivity, RH, or any finite-to-infinite statement.

The following claims remain open:

```text
R003_CCM_RHS_IDENTITY
R003_KERNEL_EF_EXTENSION
R003_CCM_BRIDGE
R003_WEIL_DISPLACEMENT
C_RH
```

## Merge gate

Exact-head run `32527178035` passed:

```text
RHRC claim and regression suite                     PASS
PR #33 cutoff-free normalization regression         PASS
lake build Zeta23.CCM                               PASS
lake build Zeta23.ExceptionalZero                   PASS
forbidden sorry / project-axiom gate               PASS
```

The new `DividedDifference` and `SourceMatrix` modules are included in the successful `Zeta23.CCM` build. No mathematical claim is promoted by this PR.

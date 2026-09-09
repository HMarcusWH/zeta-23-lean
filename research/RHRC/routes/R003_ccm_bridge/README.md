# R003 — CCM / finite Weil bridge

Status: **ACTIVE. GLOBAL FIRST-BAD + ZERO-SHIFT BRANCH RESPONSE + SOURCE-EXPLICIT CROSS-PARITY TRANSFER + EXACT SOURCE DECOMPOSITION + DENOMINATOR-FREE ZERO-SHIFT KERNEL/SOURCE TRANSPORT PROVED THROUGH PR #134. CURRENT FRONTIER = ABSOLUTE SOURCE ENERGY -> CANONICAL ONE-STEP DOMINATION. RH OPEN.**

## Current authority split

```text
live main after theorem PR #134 = 7f1fec480d1ccbff04a456ab937accf7b23cc1af
live main tree = c142efa141036331d139c532d06e7a976c5b50c2

theorem-state anchor = PR #134 merge 7f1fec480d1ccbff04a456ab937accf7b23cc1af
validated theorem head = 753ee53a7fc08bd3be9a5a0f37417629122395f9
theorem tree = c142efa141036331d139c532d06e7a976c5b50c2
RHRC #870 = SUCCESS
Permansson #643 = SUCCESS

control-plane semantic anchor = PR #117 merge 19346f4c00d13bf33db95cbe5325233f86e54c12

RH = OPEN
```

Live GitHub head + exact Lean/CI build closure remain authoritative.

## Closed internal ladder

```text
F1 finite canonical obstruction                                  PROVED / #94
constrained / Euclidean finite wall                              PROVED / #96-#98
N-FLOW fixed-L negative tail                                     PROVED / #100
PARITY reversal / displacement collapse                          PROVED / #102
PARITY-FLOW D-equivalence / exact parity geometry                 PROVED / #103
PARITY-BAD least bad size + predecessor nonnegative               PROVED / #105
FIRST-BAD-SPECTRUM compression + negative mode                    PROVED / #107
FIRST-BAD-RIGIDITY-A/B shell projection + KKT                     PROVED / #109
FIRST-BAD-RIGIDITY-C cubic parity defect finrank <=1              PROVED / #110
FIRST-BAD-RIGIDITY-D1 global first bad + W/S + exact cubic F      PROVED / #112
FIRST-BAD-RIGIDITY-D2 V=W⊕S + shifted inverse + Schur             PROVED / #113
FIRST-BAD-RIGIDITY-E1 cubic generator not inherited               PROVED / #115
FIRST-BAD-RIGIDITY-E2 canonical cubic quotient + normalized Schur PROVED / #118
FIRST-BAD-RIGIDITY-E3-A exact negative secular root iff eigenmode PROVED / #119
FIRST-BAD-RIGIDITY-E3-B2 exact explicit Schur scalar bridge       PROVED / #121
FIRST-BAD-RIGIDITY-E3-B1 projected metric/resolvent control       PROVED / #122
FIRST-BAD-RIGIDITY-E4-A1 ker(A) cubic-coupling classification     PROVED / #122
FIRST-BAD-RIGIDITY-E4-A2 kernel/range zero-shift dichotomy        PROVED / #124
FIRST-BAD-RIGIDITY-E4-A2 canonical endpoint + complete square     PROVED / #125
FIRST-BAD-RIGIDITY-E4-A3a canonical zero-shift shell response     PROVED / #127
FIRST-BAD-RIGIDITY-E4-A3b signed response + canonical kernel pole PROVED / #128
FIRST-BAD-RIGIDITY-E4-A3c source-explicit parity transfer         PROVED / #129
off-line zero -> source-explicit first-bad certificate            PROVED / #129
FIRST-BAD-RIGIDITY-E4-A4a exact source-moment decomposition       PROVED / #131
FIRST-BAD-RIGIDITY-E4-A4b0 whole-kernel source transport          PROVED / #134
FIRST-BAD-RIGIDITY-E4-A4b0 direct zero-shift parity transfer      PROVED / #134
FIRST-BAD-RIGIDITY-E4-A4b0 Gamma0*mu(z)=0 whole-kernel law        PROVED / #134
```

## Exact theorem-backed first-bad state

A hypothetical off-critical-line zeta zero forces one finite problem with:

- positive aperture `L`;
- global least-bad successor size;
- both predecessor parity sectors nonnegative;
- a genuine negative parity-compressed eigenvalue `lam<0`;
- intrinsic successor decomposition `V=W⊕S`, `dim_C S=1`;
- canonical cubic shell vector `c!=0`;
- safe shifted predecessor inverse for `lam<0`;
- exact quotient and explicit real Schur scalar root;
- exact kernel/range split `W=ker A⊕range A`;
- exact regular/resonant zero-shift classification;
- exact #127 shell response;
- exact #128 canonical kernel pole;
- exact #129 source-explicit parity transfer;
- exact #131 pole/arch/prime decomposition of the active source moment;
- exact #134 denominator-free whole-kernel source transport;
- exact #134 direct zero-shift parity transfer and whole-kernel product law.

The regular package includes

```text
Ax0=b
S0=<Tc,c>-<x0,b>
u0=-x0+c
sigma0*c = T u0
S0=star(sigma0)<c,c>
Re S0<0
Re sigma0<0
k=K(b)=0.
```

The resonant package includes

```text
k=K(b)!=0
(-lam)K(R_lam b)=k
K(R_lam b)=(-lam)^(-1)k.
```

Across parity at negative shift:

```text
F_- = alpha * F_+ + Gamma * sourceMoment(u_+).
```

At zero, #134 now proves directly:

```text
A-(Dz) = beta(z)d + mu(z)a
<b-,Dz>/rho- = beta(z)+mu(z)
beta(z)K-d + mu(z)K-a = 0
```

for `z in ker A+`, and under both preimage hypotheses:

```text
sigma- = alpha0 sigma+ + Gamma0 mu(u+0)
Gamma0 = <u-0,g->/rho-
Gamma0 * mu(z)=0  for every z in ker A+.
```

No zero-shift inverse, pseudoinverse, Laurent expansion, one-dimensional-kernel assumption, D-isometry, source sign, or coefficient nonzeroness is used.

## Current route

### A4b1 — absolute canonical source energy

**OPEN / NEXT THEOREM.**

Lift the production source decomposition from the shift-invariant #131 normal moment to

```text
E(v)=Re<Tv,v>
```

while retaining the canonical archimedean scalar identity correction.

The first theorem package should expose exact energy bookkeeping:

```text
pole energy
- reduced arch diagonal energy
- reduced arch off-diagonal energy
- arch scalar correction * ||v||^2
- finite von-Mangoldt-weighted prime atom energies.
```

Specialize to the canonical cubic shell and `cubicZeroShiftTrialVector`. Under `Ax0=b`, theoremize the exact regular energy/Schur identity. Do not promote positivity merely from the decomposition.

### A4b2 — canonical one-step domination

**OPEN / DECISIVE TARGET.**

For either parity, define

```text
A=P_W T|_W
b=P_W T c
q_c=Re<Tc,c>.
```

Prove from the actual canonical source

```text
q_c >= 0
|<w,b>|^2 <= q_c Re<Aw,w>  for every w in W.
```

If proved:

```text
w in ker A -> <w,b>=0
```

so resonance disappears. In the regular branch, `Ax0=b` gives `S0>=0`, contradicting the already-proved `Re S0<0` at the forced negative root.

This is the main unresolved finite arithmetic/coercive theorem.

### A4R — regular-aperture log-lift

**LEAD / OPTIONAL SIMPLIFIER.**

If resonance materially complicates A4b2, frozen-cutoff analyticity and

```text
M_Q(L)=-log(L)I+B_Q(L),  L=exp(z)
```

may yield dense apertures with injective predecessor parity blocks. Preserve a negative witness by continuity and reselect the least-bad size.

Positive-definite predecessors do not by themselves exclude a negative successor.

## Exact countermodel firewall

Exact rational generic centered-grid reversal-symmetric diagonal fixtures preserve the legal parity/boundary-flat/KKT/rank-one/transfer structure while realizing:

```text
sourceMoment(u+) != 0 with Gamma = 0 at a common negative root
Gamma != 0 with sourceMoment(u+) = 0 at a common negative root
alpha = 0 at an odd-only negative root with positive even successor
```

Additional fixtures realize negative `Gamma`, negative `alpha`, and either sign of the source moment.

These fixtures are not `canonicalSourceMatrix` and are not zeta/RH counterexamples. They quarantine generic factorwise sign/nonzero closure, division by unproved factors, and even-only exclusion.

## Absolute-origin firewall

Under the generic simultaneous shift

```text
M -> M+tI
lambda -> lambda+t,
```

the trial/transfer package can remain unchanged while the spectrum moves relative to zero. Therefore shift-invariant cross-parity data cannot determine absolute negative spectral sign.

The final source argument must retain the exact canonical scalar normalization. This is why absolute source energy is primary after #134.

## Quantitative source lead

Boundary-flat Taylor algebra predicts first potentially nonzero source-coordinate terms at orders `omega^7` / `omega^9`. High-precision checks support the predicted leading coefficients. This remains **DERIVED / EXPERIMENTAL**, not theorem authority, and should be formalized only if it feeds a rigorous source-energy/coercivity estimate.

## Permanent normalization / model firewalls

- canonical sign-sensitive object is `canonicalSourceMatrix = cutoffFreeMatrix = sourceEq44Matrix = dictionaryMatrix` under the repaired source convention;
- legacy printed `finiteMatrix` differs by a scalar identity, so absolute eigenvalue/PSD/inertia claims do not transfer automatically;
- generic R002 smooth taper-grid is not the canonical CCM family except at exact specialization;
- Bombieri zero-height truncations are distinct from deterministic CCM Fourier-mode truncations;
- boundary-flat legality is required for the hard-window C² bridge;
- `ker A` is not the predecessor-size compressed-operator kernel;
- no `A^-1` at zero;
- `Re S0<0` and `Re sigma0<0` are not branch exclusion by themselves;
- `Gamma0*mu(z)=0` is a product law, not factorwise exclusion;
- the exact resonant pole is not automatically contradictory;
- D is algebraic, not unitary/isometric;
- the predecessor correction in `D c+` may not be dropped;
- no division by `alpha`, `Gamma`, overlap or source moment without separately proved nonzeroness;
- factorwise transfer closure is quarantined by exact rational countermodels;
- shift-invariant transfer data cannot locate the absolute spectral origin;
- positive-definite predecessors do not imply a positive successor;
- generic structural countermodels do not refute `canonicalSourceMatrix`;
- root uniqueness is not root exclusion;
- numerical precision is not theorem authority;
- RH remains OPEN.

Detailed current implications and falsification plan: `../../RESEARCH_LEADS_POST_134_DELTA.md`.

**RH remains OPEN.**

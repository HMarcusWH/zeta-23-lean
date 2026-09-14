# Post-#170 Schur-visibility / threshold-barrier research delta

> **Claim firewall: RH remains OPEN.**
>
> This is a research-state synthesis. It records exact executable identities, finite Arb certificates, and experimental discovery results. It does **not** promote any post-#163 result to Lean theorem authority.

## Authority split

Live GitHub head + exact compiler/CI evidence are authoritative dynamically.

### Theorem authority

```text
latest theorem-bearing PR = #163
validated theorem head = b418ff034428f92594bab0e5b8276181a086ee4b
validated theorem tree = c397b3a015ea54e38ecfe626d6e29556fe963839
RHRC #1039 = SUCCESS
Permansson #812 = SUCCESS
```

### Latest research-evidence anchor

```text
latest merged research PR = #170
validated research head = 70689692d5b92252bf9da97740385aaced2bf197
merged research commit = c94242fe41ae62b59aaa392a33e35034eb2c1b1e
research tree = 38e38a1d4cf90afa0e8103e58d1cbae626ebdeef
RHRC #1058 = SUCCESS
Permansson #831 = SUCCESS
```

### Control authority

```text
control-plane semantic anchor = PR #117
selected formal first break = E4A4-SCHUR-FB-05
terminal claim = RH_OPEN
```

Research PRs #165-#170 change the discovery/routing state only. The theorem and machine-claim surfaces remain unchanged.

## What #170 changed

PR #170 replaces the arbitrary final Sylvester coordinate used in the post-#167 discovery tooling with the theorem-aligned one-step geometry

```text
B_step = [W | c]
```

where `W` is the exact centered predecessor basis and `c` is the exact nonzero shell generator. In this basis

```text
H = [[A,b],[b^T,d]]
P = d - b^T A^-1 b.
```

Because the checked-in integer shell generator is only ray-equivalent to Lean's canonical cubic shell, the scale-invariant research quantity is

```text
P_hat = P / ||c||^2.
```

The deterministic acceptance layer verifies that this unit-shell pivot agrees with the existing post-#150 selected-residual Schur energy on production fixtures.

## Exact executable algebra locked by #170

The research checker validates the finite-dimensional rank-one Schur update

```text
P(H + tau*v*v^T)
  = P(H) + tau*rho^2/(1 + tau*gamma)
```

with

```text
rho   = alpha - a^T A^-1 b
gamma = a^T A^-1 a
v     = (a, alpha).
```

It also validates the exact directional Schur derivative identity

```text
DP_H[D]
  = D_d - 2*D_b^T A^-1 b + (A^-1 b)^T D_A (A^-1 b).
```

Equivalently, for the zero-shift Schur-minimizing trial `u = c - W A^-1 b`, this is the finite-dimensional envelope identity

```text
DP_M[D] = u^T D u.
```

This identity was already known in the project as a diagnostic inside DR-022. #170 locks it in the executable theorem-aligned `[W|c]` research coordinate. It remains **EXACT EXECUTABLE**, not Lean theorem authority.

## q=17 theorem-aligned threshold result

For the near-critical target

```text
q = 17
N = 3
K* = 4
parity = odd
```

Arb certifies the predecessor block positive at the threshold and encloses a positive unit-shell pivot

```text
P_hat(log 17) ~= 1.25103182564e-9 > 0.
```

The threshold `M3` direction is Schur-visible:

```text
rho ~= -35.0364240415
rho != 0   [Arb certified at the checked finite state].
```

Therefore the favorable seventh-order odd prime-entry jet from #168 is not annihilated by the one-step Schur minimization.

## Arithmetic kick versus smooth background

At all seven checked positive source-coordinate offsets, Arb certifies the exact entering-q contribution raises the raw theorem-aligned pivot:

```text
exact q=17 pivot effect > 0  at 7/7 checked offsets.
```

The leading rank-one model agrees asymptotically with the exact atom. The residual has the expected higher-order behavior in the checked finite regime.

Independently, after removing the signed entering-q atom at the same aperture, the smooth background has a negative central finite-difference enclosure at all seven tested scales. The values stabilize numerically near

```text
-4.595899e-8
```

for the unit-shell pivot as a function of the source coordinate.

This is **RIGOROUS FINITE-DIFFERENCE EVIDENCE**, not a derivative theorem or global sign theorem.

## Physical threshold-to-threshold scout

The direct production scout from `log 17` toward the next genuine von-Mangoldt seam `log 19` records

```text
97 / 97 sampled states H1-aligned
0 sampled negative pivots
minimum sampled unit-shell pivot ~= 4.32e-10 > 0.
```

This is discovery evidence only. It is not interval positivity on the whole cell.

## Research conclusion after #170

The post-#168 matrix-level picture now descends to the theorem-aligned scalar obstruction:

```text
entering q=17 arithmetic atom  -> raises Schur pivot
smooth q-removed background    -> lowers Schur pivot locally
full sampled physical state    -> remains positive through q=19.
```

Thus the isolated arithmetic kick is both nonzero and Schur-visible, but it does not by itself determine the complete pivot motion.

The unresolved mathematical problem is no longer to construct the pivot/background decomposition. #170 has done that in the executable research layer.

The new target is to control the **integrated Schur-envelope dynamics between arithmetic seams**.

## Next research target: threshold-to-threshold Schur barrier

For an H1 state let

```text
P(L) = d(L) - b(L)^T A(L)^-1 b(L)
u_L  = c - W A(L)^-1 b(L).
```

The local envelope identity gives, where differentiability is available,

```text
P'(L) = u_L^T M'(L) u_L.
```

The useful fact is not a global fixed sign. The project already quarantines global Schur monotonicity in DR-022.

Instead, the next research problem is to control

```text
P(L_next^-) - P(L_q^+)
  = integral_{L_q}^{L_next} P'(L) dL
```

relative to the positive barrier available after an arithmetic seam and the high-order replenishment supplied by the next entering prime power.

Highest-information questions:

1. How large can the integrated smooth-background loss be before the next nonzero von-Mangoldt threshold?
2. Which exact pole/archimedean/active-prime/scalar derivative contributions create the near-cancellation seen at q=17?
3. Is the tiny net drift structurally constrained or accidental?
4. Can the pivot reach zero while H1 remains valid before the next arithmetic seam?
5. Does the parity-asymmetric seventh/ninth-order arithmetic replenishment create a useful threshold barrier?
6. Does any such mechanism survive across several q, N, and both parities?

## Algebraic firewall: channel pivots are not additive

The scalar Schur map is nonlinear:

```text
P(M1 + M2) != P(M1) + P(M2)
```

in general.

Therefore pole/archimedean/prime/scalar **pivot values may not be added**.

Channel attribution is cancellation-preserving only at matrix level or through the directional/envelope derivative evaluated at the complete minimizing trial:

```text
DP_M[D] = u_M^T D u_M.
```

This should become a permanent obstruction-ledger warning.

## Dead-route firewall

The next threshold-barrier pass is **not** a revival of DR-022.

DR-022 quarantines the claim that the minimizing Schur pivot has one fixed derivative sign globally. Post-#150 experiments already show sign changes.

The active route instead asks for local/integrated control over one arithmetic interval at a time, preserving exact canonical cancellation and allowing the derivative to change sign.

## What #170 does not establish

It does not prove:

```text
rho != 0 at every threshold/state
P'(L) < 0 or > 0 on any whole interval
whole-cell positivity from q=17 to q=19
an integrated threshold barrier
a simultaneous-parity exclusion
odd-selected closure
sourceMoment <-> M4 rigidity
endpoint-scalar sign/nonvanishing
negative-root exclusion
RiemannHypothesis.
```

The finite Arb central differences are not derivative theorems. The 97-point scout is not interval certification. The executable Schur identities are not Lean theorem authority.

## Highest-leverage next move

Build a research PR that uses the theorem-aligned Schur envelope locally to estimate/certify **barrier loss versus arithmetic replenishment from one nonzero von-Mangoldt seam to the next**, with broad q/N/parity falsification.

If that mechanism survives and supplies an independent inequality unavailable from successor positivity itself, theoremize only the weakest useful statement and compose it with the exact retained #161/#163 state.

**FB-05 remains OPEN. RH remains OPEN.**

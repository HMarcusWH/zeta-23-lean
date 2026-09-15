# RHRC current research plan

> **Claim firewall: RH remains OPEN.**

Live GitHub head + exact compiler/CI evidence are authoritative dynamically. This file records the current theorem, research and control anchors and the active FB-05 execution order.

## Authority split

### Theorem authority

```text
latest theorem-bearing PR = #184
validated theorem head = a756494ebe7e2530715e996b9a9a341fbe07c683
merged theorem commit = 6f04e94473eb112b59eeaa2c6fc6ac6cbe7fe30e
validated theorem tree = 6c77cd470809959a403b3bcc5f08d39f4076fa4c
RHRC #1089 = SUCCESS
Permansson #862 = SUCCESS
```

### Latest research-evidence anchor

```text
latest merged research PR = #186
validated research head = 7d277a99437d98fdb7c831f25a130eac07f1b3af
merged research commit = 0494658a87d29eeb2124aa16232c264c21d23c18
RHRC #1091 = SUCCESS
Permansson #864 = SUCCESS
research disposition = DOMINATION_SIGNAL_MIXED
```

### Control authority

```text
control-plane semantic anchor = PR #117
selected formal first break = E4A4-SCHUR-FB-05
terminal claim = RH_OPEN
```

The theorem, research and control anchors are intentionally separate. #184 remains theorem authority; #186 advances research-only evidence; #117 remains controller semantic authority.

## One-screen frontier

```text
PROVED THROUGH #184
  off-line zero
  -> retained regular cell-minimal first-bad certificate
  -> exact negative canonical source channel
  -> exact finite pole-prime discrepancy
  -> legal production Riesz engine and transformed negativity
  -> same-state shifted source/Riesz composition
  -> mixed quadratic-normal seventh jet
  -> exact finite-prime sampling of same observable
  -> exact R8-R9 squared-jet boundary
  -> generic real 2x2 Schur-envelope derivative                    #182
  -> generic complex-Hermitian 2x2 Schur calculus                  #184
  -> full frozen parity family on logarithmic cover                #184
  -> exact fixed-cell bridge to parityCompressedCanonical          #184
  -> N2 predecessor / cubic-shell reconstruction + orthogonality   #184
  -> algebraic P_t' = -envelopeNormSq + remainderEnvelopeDerivative #184
  -> remainderEnvelopeDerivative < envelopeNormSq -> P_t' < 0      #184

RESEARCHED THROUGH #186
  q13/N2/K3/even reduced to exact 2x2 scalar barrier
  fixed-unit physical-L derivative backend validated
  exact-center six-point Q14 derivative basin minimum-oriented      #180
  coordinate-correct universal/remainder drift decomposition        #186
  primary exact-center domination signal = MIXED                     #186
  finite-width scope = FINITE_WIDTH_OUT_OF_H1_SCOPE                  #186

NOW — FB-05
  the simple universal source-remainder domination conjecture is not the next theorem target.
  Instead:
    -> explain the exact-center mixed split without moving/refitting the frozen schedule
    -> identify a canonical local discriminator for the two positive-margin states versus the four negative-margin states
    -> test the discriminator on ancestry/parity/aperture controls
    -> only after surviving falsification, state the narrowest theorem candidate
    -> keep actual production scalar derivative witnesses as useful formal infrastructure, but separate them from any unproved sign law
```

## Exact #184 theorem package

PR #184 adds `Zeta23/CCM/HermitianSchurEnvelopeDerivative.lean` and `Zeta23/CCM/FrozenN2SchurLogDrift.lean` to the aggregate CCM build.

For a Hermitian 2x2 block with real diagonal coordinates `a,d` and complex off-diagonal coordinate `b`, Lean theoremizes the Schur pivot/determinant calculus with the correction `|b|^2/a`, including real-component `HasDerivAt` theorems for `Re b` and `Im b`. At contact and under H1, determinant and pivot derivative orientations agree.

The frozen production family is theoremized on logarithmic coordinate `t` as

```text
M~(t) = -t I + R~(t),
```

with exact fixed-cell equality to the actual production `parityCompressedCanonical`. For N2/K3, #184 also proves predecessor/shell reconstruction, nonzero canonical cubic shell and predecessor-shell orthogonality.

For derivative data having the required coordinate form, #184 proves

```text
P_t' = - envelopeNormSq + remainderEnvelopeDerivative
```

and therefore

```text
remainderEnvelopeDerivative < envelopeNormSq -> P_t' < 0.
```

### Exact #184 firewall

#184 is conditional at the sign step. It does not prove the production arithmetic remainder satisfies the domination inequality. It does not prove contact existence/uniqueness, an opposing first-bad crossing orientation, global Schur monotonicity, first-bad exclusion, negative-root exclusion or RH.

## Exact #186 research result

PR #186 reused the exact frozen #180 q13/Q14 N2/K3/even schedule and the existing physical-`L` derivative backend. It did not move centers, refit the basin or promote numerical/Arb output to theorem authority.

It evaluated the coordinate-correct decomposition

```text
P_L' = -E/L + R_L'
margin_L = E/L - R_L'
rho_L = L*R_L'/E
```

with rigorous consistency checks between the full derivative and reconstructed universal-plus-remainder split.

The exact primary-center disposition is:

```text
DOMINATION_SIGNAL_MIXED

POSITIVE margin:
  det_left_o2^-10_r2^-13
  det_left_o2^-13_r2^-16

NEGATIVE margin:
  det_right_o2^-10_r2^-13
  det_right_o2^-13_r2^-16
  det_left_o2^-16_r2^-19
  det_right_o2^-16_r2^-19

UNRESOLVED primary exact centers: none
finite-width scope: FINITE_WIDTH_OUT_OF_H1_SCOPE
```

### What #186 kills

The simple statement “the actual production remainder is dominated by the universal negative log drift on the dangerous frozen states” is false in the tested scope. Therefore a theorem effort aimed directly at a universal `R_t' < E` or physical `R_L' < E/L` law would be research-misaligned unless its hypotheses are narrowed by a newly identified canonical condition.

### What #186 does not kill

- #184's conditional theorem remains valid.
- Local domination can still hold on a meaningful subclass; two frozen centers do satisfy it.
- A contact-local law may differ from a law over arbitrary side points.
- A different independent canonical invariant could still supply the required same-state contradiction.
- The production scalar derivative-witness bridge remains useful formal infrastructure.

## Active lead A — explain the mixed split

This is now the highest-information research move.

Freeze the #186 schedule and compare the two positive-margin states against the four negative-margin states. Candidate diagnostics must be canonical or theorem-connectable; do not fit an arbitrary classifier to six points.

Prioritize quantities already attached to the production geometry:

```text
E
R_L'
rho_L = L*R_L'/E
P_L'
a, |b|, d
x=b/a or |b|/a in the Hermitian normalization
shell/predecessor norm balance
prime-threshold location within the fixed-Q cell
left/right basin position relative to the #180 oriented minimum
same-Q ancestry/parity controls
```

The key question is whether the mixed split is explained by a structural boundary/contact variable rather than accidental six-point numerics.

Fast falsifiers for any proposed discriminator:

1. it changes sign/order under an innocuous normalization;
2. it fails on the inherited odd-N2 ancestry control;
3. it only separates the already-labelled left/right samples and has no theorem route to contact;
4. it silently assumes H1 on finite-width boxes where #186 says H1 is not certified;
5. it is equivalent to successor positivity or to the target sign itself.

## Active lead B — actual production derivative witnesses

The repo already proves entrywise holomorphy of the complete frozen complex source remainder on the punctured safe strip. A formal bridge can still transport that analyticity through exact parity projection and N2 predecessor/canonical-shell pairings to real derivatives of the remainder scalar coordinates.

Target infrastructure:

```text
complex frozen-source remainder holomorphy
  -> parity-compressed remainder scalar analyticity
  -> N2 predecessor/shell pairings
  -> derivatives of a_R, Re b_R, Im b_R, d_R
  -> actual production HasDerivAt Schur identity
```

This theorem package would remove an interface gap. After #186 it must **not** be sold as evidence that a universal domination theorem should follow.

## Active lead C — same-state incompatibility search

Pair A remains viable only in a narrowed form. The contradiction still requires two independently meaningful incompatible properties of the exact same retained state/contact.

Possible routes now include:

```text
A1 contact-local orientation law with a newly discovered canonical discriminator
B  negative-index vs localized sampling rigidity
C  local first-bad vs short-window zero rigidity
D  two-parity squeeze
E  off-line growth vs structured finite-energy control
```

The mixed #186 result raises the relative value of B-D because a universal Pair-A domination law no longer looks plausible.

## Finite-width H1 lane

The nonzero-width primary boxes remain outside certified H1 scope. If a future local discriminator needs neighborhoods, use the established order:

```text
1. centered H1 recovery from point a(L0)>0 and rigorous a'(I)
2. retry the Schur/remainder quantity only inside certified H1
3. add second-derivative centered propagation if needed
4. interval Newton/Krawczyk only after signed neighborhoods exist
```

Do not revive raw subdivision with only more precision/depth.

## What remains formally open

```text
explicitCanonicalSourceMoment != 0 -> M4 != 0
M4 != 0 -> explicitCanonicalSourceMoment != 0
finite production samples determine h^(7)(0)
canonicalPolePrimeRieszEndpointScalar L 8 >= 0
canonicalPolePrimeRieszEndpointScalar L 8 != 0
actual N2 production remainder scalar derivative witnesses
actual production HasDerivAt Schur log-drift identity
any valid narrowed source-specific contact-orientation law
first-bad contact existence/orientation composition on the same retained state
centered finite-width H1 on the #180/#186 boxes
q13/N2/K3/even whole-cell sign/contact/nonvanishing
simultaneous even/odd bad exclusion
odd-selected first-bad closure
independent contradiction-producing canonical arithmetic restriction
negative-root exclusion
outside-strip/trivial-zero terminal seam
RiemannHypothesis
```

## Reusable firewalls

- #186 is a research certificate, not Lean theorem authority;
- `DOMINATION_SIGNAL_MIXED` kills the simple universal domination hypothesis only in its tested scope;
- two positive centers are not a theorem and four negative centers are not a theorem;
- `t=log L` and physical `L` derivatives must retain the factor of `L`;
- determinant and pivot minima are distinct because `P=Delta/a` and `a(L)` varies;
- finite-width Schur/remainder statements require certified H1;
- global aperture/global minimizing-Schur monotonicity remains quarantined;
- q13/N2/K3 evidence does not automatically generalize to every retained first-bad state;
- no proposed discriminator may merely restate successor positivity;
- RH remains OPEN.

## Highest-leverage next move

Perform a **post-#186 mixed-split discriminator audit** on the exact same frozen schedule. The objective is not to rescue the discarded universal law; it is to determine whether the two surviving positive-margin states share a canonical, theorem-connectable condition absent from the four failures.

Standing question:

> What mathematically meaningful local variable explains why the production remainder loses to the universal drift at exactly two tested states but outruns it at four, and does that variable attach to the actual first-bad/contact state rather than to our sampling choices?

Only if such a condition survives controls should it become a new theorem target.

Detailed newest synthesis:
`RESEARCH_LEADS_POST_186_REMAINDER_DRIFT_MIXED_DELTA.md`.

**RH remains OPEN.**

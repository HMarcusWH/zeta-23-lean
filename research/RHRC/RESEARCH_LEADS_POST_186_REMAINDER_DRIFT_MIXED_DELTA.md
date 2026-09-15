# Post-#186 research delta — remainder-drift falsification

> **Claim firewall: RH remains OPEN.**
>
> This is a research-state delta. It does not promote executable/Arb evidence to theorem authority.

## Exact authority checked

```text
THEOREM AUTHORITY
PR #184
validated theorem head = a756494ebe7e2530715e996b9a9a341fbe07c683
merged theorem commit = 6f04e94473eb112b59eeaa2c6fc6ac6cbe7fe30e
validated theorem tree = 6c77cd470809959a403b3bcc5f08d39f4076fa4c
RHRC #1089 = SUCCESS
Permansson #862 = SUCCESS

RESEARCH AUTHORITY
PR #186
validated research head = 7d277a99437d98fdb7c831f25a130eac07f1b3af
merged research commit = 0494658a87d29eeb2124aa16232c264c21d23c18
RHRC #1091 = SUCCESS
Permansson #864 = SUCCESS
research disposition = DOMINATION_SIGNAL_MIXED

CONTROL AUTHORITY
PR #117
selected first break = E4A4-SCHUR-FB-05
terminal claim = RH_OPEN
```

# What became formally true

No new Lean theorem became true in #186. Formal mathematical authority remains exactly #184.

The #184 theorem package still proves the complex-Hermitian N2 Schur calculus, frozen production log-cover decomposition, fixed-cell bridge, predecessor/canonical-shell geometry, algebraic envelope derivative split

```text
P_t' = -E + R_t'
```

and the conditional implication

```text
R_t' < E -> P_t' < 0.
```

# What became research-certified

PR #186 reused the exact frozen #180 q13/Q14 N2/K3/even schedule and existing complete physical-`L` derivative backend. It implemented and rigorously cross-checked

```text
P_L' = -E/L + R_L'
margin_L = E/L - R_L'
rho_L = L*R_L'/E.
```

The green certificate returned

```text
DOMINATION_SIGNAL_MIXED
```

with:

```text
POSITIVE margin
  det_left_o2^-10_r2^-13
  det_left_o2^-13_r2^-16

NEGATIVE margin
  det_right_o2^-10_r2^-13
  det_right_o2^-13_r2^-16
  det_left_o2^-16_r2^-19
  det_right_o2^-16_r2^-19

UNRESOLVED primary exact centers
  none

FINITE-WIDTH SCOPE
  FINITE_WIDTH_OUT_OF_H1_SCOPE
```

The certificate also keeps theorem promotion, FB-05 closure, negative-root exclusion and RH claims false.

# What changed

Before #186, the post-#184 lead was:

```text
maybe the actual production remainder is always too small to outrun the universal -E drift
```

in the dangerous frozen q13/Q14 microscope.

After #186, that broad formulation is no longer viable in the tested scope. Four of six primary exact centers certify the opposite margin sign. The correct conclusion is not “the drift route failed”; it is narrower:

```text
unconditional local domination is false on the frozen panel;
conditional/local domination still occurs at two states;
the missing information is what distinguishes those states.
```

This changes the research target from proving a magnitude inequality to discovering the condition under which that inequality is true and whether that condition attaches to the actual first-bad/contact state.

# Upstream implications

1. **Do not strengthen #184 in the wrong direction.** The algebraic theorem is correct; the missing arithmetic inequality cannot be added universally without new hypotheses.
2. **Keep the production derivative-witness bridge modular.** It remains valuable as exact infrastructure, but it should expose the remainder derivative rather than bake in a sign claim.
3. **Prefer invariant/local coordinates.** A useful new hypothesis should be expressible in theorem-backed production geometry, not in ad hoc labels of the six samples.
4. **The coordinate conversion is validated operationally.** The falsifier used physical `L` consistently with `d/dt = L d/dL`; no rescue can come from mixing the two coordinates.

# Downstream implications

The immediate Pair-A route is now conditional:

```text
canonical discriminator C(state)
  -> contact-local R_t' < E
  -> #184 gives P_t' < 0 at contact
  -> independent first-bad theorem gives incompatible orientation
  -> same-state contradiction
```

Without the first arrow, Pair A does not close.

This raises the relative value of alternative FB-05 compositions already in the incompatibility program:

```text
negative-index vs localized sampling rigidity
local first-bad vs short-window zero rigidity
two-parity squeeze
off-line growth vs structured finite-energy control
```

# Resurrected routes

The mixed sign pattern makes several previously secondary questions worth reopening:

- whether the sign transition is tied to position relative to the #180 minimum-oriented basin;
- whether the left/right asymmetry is a genuine contact-orientation clue or merely a sampling artifact;
- whether parity/ancestry controls distinguish the same states;
- whether a shell/predecessor norm ratio or normalized coupling controls `rho_L`;
- whether the correct theorem is contact-local rather than side-neighborhood/global.

Global Schur monotonicity is **not** resurrected. The data remain compatible with local sign changes and the project quarantine stays in force.

# New RH-relevant clues

## LEAD — a state-dependent drift barrier

The universal term is fixed by geometry, while the arithmetic remainder sometimes loses and sometimes wins. This suggests the useful object may be a dimensionless state variable controlling

```text
rho_L = L*R_L'/E.
```

A theorem of the form

```text
C(state) -> rho_L < 1
```

could be useful if `C` is independently forced by first-bad/contact geometry. The value is in the composition, not in domination by itself.

## LEAD — contact may be more rigid than side samples

#186 tests frozen side centers, not an established exact contact. A mixed side pattern does not exclude a one-sided law exactly at first contact. This is worth testing only if contact can be localized without assuming the desired sign.

## LEAD — two-parity information may supply the missing selector

Because the canonical arithmetic source is parity-sensitive and the project already carries cross-parity transfer structure, the missing condition may involve an opposite-parity quantity rather than a same-channel norm ratio.

# Falsification checks

Any proposed post-#186 discriminator must survive:

1. **Frozen-panel test:** no moving/refitting the #186 centers.
2. **Normalization test:** invariant under harmless basis/shell rescaling or explicitly theorem-normalized.
3. **Same-state test:** evaluated on the same production object/aperture/parity that will enter the contradiction.
4. **Control test:** check inherited odd-N2 ancestry and nearby fixed-Q controls.
5. **Target-leakage test:** the discriminator cannot simply contain `margin_L`, `rho_L<1`, successor positivity, or another algebraic restatement of the desired conclusion.
6. **H1 test:** no interval claim outside certified H1.
7. **Sparse-exception test:** a route intended for global zero exclusion must not ignore thin exceptional sets.
8. **Mustache test:** growth/zero-distribution claims must be checked against known analogous systems where the desired conclusion fails.

# Highest-leverage next moves

1. **RESEARCH:** run a fixed-schedule mixed-split audit. Emit a compact table for all #186 primary and control states with `E`, `R_L'`, `rho_L`, `P_L'`, `a`, coupling/norm ratios, cell position and ancestry/parity metadata. Predeclare candidate discriminators before judging them.
2. **RESEARCH:** test whether the sign transition is explained by location relative to the #180 minimum or by a production-specific invariant independent of left/right labels.
3. **THEOREM INFRASTRUCTURE:** package actual production remainder scalar derivative witnesses/`HasDerivAt` transport from existing complex holomorphy. Keep it sign-neutral.
4. **COMPOSITION:** if a discriminator survives, state the narrowest contact-local inequality and separately prove the opposing first-bad orientation on exactly the same state.
5. **FALLBACK:** if no theorem-connectable discriminator survives, downgrade Pair A and prioritize the negative-index/sampling, parity-squeeze and local-zero-rigidity incompatibility pairs.

# Standing questions

> Given everything now formally true, what becomes possible that was not possible before?

We can now measure the production remainder against the exact theoremized universal drift in the correct coordinate and know that the answer is genuinely state-dependent on the dangerous finite panel.

> If this contains a clue toward RH, where does that clue propagate?

It propagates into the search for a **selector condition**: a canonical property of the retained first-bad/contact state that forces the useful side of the mixed inequality.

> What experiment or lemma most efficiently tells us whether that clue is real?

Freeze the #186 states, predeclare a small set of theorem-connectable dimensionless candidates, and test whether any one separates the positive-margin states from failures while also surviving ancestry/parity controls. If none does, stop investing in Pair-A domination and move to the next incompatibility pair.

**RH remains OPEN.**

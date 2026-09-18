# Post-#215 research delta — retained negative-root secular frontier

> **Claim firewall: RH remains OPEN.**

## Exact checked state

```text
THEOREM AUTHORITY
PR #213
head  = 703c3764a7d35aa4801e791a1929efa54c2533a1
merge = ee341a6071d177c75bbea0a5f92ebe3b3bb16696
tree  = db00686b2bbb821adb857e5c68f422d19c4f91cd

RESEARCH AUTHORITY
PR #215
head  = 5469fbac77c82ccfc9dad0da4c7ce2b0ba67c47a
merge = 191b1b648448c92010286dae54df8502df1f55ce
tree  = 4e6111c974ae8abbf59a5063d4b1ea760fa39ffd

CONTROL SEMANTIC AUTHORITY
PR #117

RH = OPEN
```

# What became formally true

**PROVED:** no new Lean theorem became true in #215. The theorem frontier remains #213.

**EXPERIMENTAL SIGNAL / rigorous bounded Arb research:** on the exact frozen K=3 even boundary-flat carrier, #215 certified `FULL_SPACE_DUAL_INDEPENDENCE_CERTIFIED`, `FULL_SPACE_SIGN_INDEFINITE_CERTIFIED`, and `DUAL_INDEPENDENCE_SURVIVES_Q13_Q15_CONTROLS`.

Exact geometry:
```text
dimension = 2
M4 covector = (24,144)
D-energy Gram = [[40,72],[72,180]]
det(D-energy Gram) = 2016
```

Q14:
```text
wedge = [-7.92856142933793718521707742118e-7 +/- 2.44e-37]
R_min = [-7.60547660138399452560501190345e-11 +/- 1.90e-41]
R_max = [1.02497161190896926446719955942e-6 +/- 3.03e-36]
```

# What changed

Universal full-carrier source/M4 sign and proportionality are consumed in the frozen research scope. The retained eigenmode / first-bad restriction was `NOT_TESTED`.

The repository-wide dumbassery check also found that the retained object is a negative secular root at fixed aperture; fixed-cell witness persistence gives strict negativity on an open neighborhood, not a same-state zero crossing. Contact is therefore a lead, not the next bridge.

# Upstream implications

Reuse the exact old same-root secular stack:
`crossParityFirstBadRootCertificate` and
`cubicSecularScalar_odd_eq_overlap_mul_source_of_even_root`.

In the even-selected branch:
```text
F_plus(lambda) = 0
F_minus(lambda) = Gamma(lambda) * S(v_lambda)
```
at the same `L`, `N`, and `lambda < 0`.

# Downstream implications

The next theorem-extraction question is whether opposite-good forces `0 < re(F_opposite(lambda))` at the same negative shift. If it does, the exact cross-parity identity becomes a strict signed constraint which can be composed with #209:
```text
-lambda * ||D v_lambda||^2
  <= re(star(S(v_lambda))*M4(v_lambda)).
```

# Resurrected routes

**Zero shift:** selected regular response is already strictly negative; exact cross-parity zero-shift transfer exists if both preimages exist. Candidate missing bridge: opposite-good successor -> cubic coupling annihilates predecessor kernel -> zero-shift preimage.

**Resonant branch:** exact kernel response scales like `1/(-lambda)`. Test only after obtaining a retained spectral tube and an independent lower coupling bound.

**Large aperture:** `ExceptionalZero.ApertureFreedom` means eventual large-`L` incompatibility may suffice.

# New RH-relevant clues

**LEAD / HYPOTHESIS:** derive an exact secular-completion identity of the structural form
```text
||c_-||^2 * F_-(lambda)
  = re(star(S)*M4) - |S|^2 * C(lambda),
C(lambda) >= 0.
```
This is a **HYPOTHESIS / template**, not a result. Orientation, conjugation, constants and correction terms remain to be derived.

**LEAD:** zero-shift response-range closure.

**LEAD:** resonant `1/(-lambda)` budget blow-up.

# Falsification checks

1. Prove or refute the strict opposite-good secular sign from exact definitions.
2. Check whether `Gamma(lambda)` can vanish or flip orientation.
3. Derive all conjugations exactly.
4. Verify the proposed resolvent correction sign rather than assuming it.
5. Keep simultaneous odd-bad and odd-selected branches open.
6. Do not import #215 arbitrary-vector signs into retained-eigenmode claims.
7. Do not move to contact without a same-state theorem.
8. Test generic Hermitian block analogues for disguised successor-positivity restatements.

# Highest-leverage next moves

```text
1. theorem-audit opposite-good secular scalar at lambda < 0
2. derive exact Gamma*S completion from existing cross-parity definitions
3. preregister a retained-state falsifier on that exact formula
4. theoremize only a surviving independent inequality
5. in parallel test the zero-shift range lemma
6. test resonant pole blow-up only with an independent coupling lower bound
```

Next research target: `RETAINED_CROSS_PARITY_SECULAR_COMPLETION`.

# Standing questions

**What becomes possible now?** The old same-root cross-parity transfer can finally be composed with an exact complete source functional and quantitative source/M4 coercivity.

**Where does the clue propagate?** Into retained secular dynamics, zero-shift response, and resonant kernel structure—not arbitrary carrier vectors.

**What is the cheapest discriminator?** Exact opposite-good secular sign plus an algebraic audit of `Gamma(lambda) * S(v_lambda)`.

**RH remains OPEN.**

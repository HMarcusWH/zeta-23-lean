# RHRC research leads — post-PR #134 delta

> **Authority note:** this file records the post-green research interpretation of merged theorem PR #134. Exact Lean declarations + exact successful CI remain authoritative. **RH remains OPEN.**

## Exact green object

```text
PR #134 = FIRST-BAD-RIGIDITY-E4-A4b0: exact zero-shift kernel/source transport
validated theorem head = 753ee53a7fc08bd3be9a5a0f37417629122395f9
merged main = 7f1fec480d1ccbff04a456ab937accf7b23cc1af
merged tree = c142efa141036331d139c532d06e7a976c5b50c2
RHRC #870 = SUCCESS
Permansson #643 = SUCCESS
RH = OPEN
```

The PR changed only the theorem layer needed for zero-shift transport:

- `Zeta23/CCM/KernelSourceTransport.lean` — new;
- `Zeta23/CCM/ZeroShiftCrossParityTransfer.lean` — new;
- `Zeta23/CCM.lean` — imports both into the validated CCM build closure.

No terminal RH theorem, negative-root exclusion theorem, source-sign theorem, or machine claim promotion was added.

## What became formally true

### PROVED — denominator-free whole-kernel transport

For every even predecessor-kernel vector `z`, the exact production source functional from PR #131 satisfies

```text
A-(Dz) = beta(z)d + mu(z)a
<b-,Dz>/rho- = beta(z)+mu(z).
```

Projecting to the whole odd predecessor kernel gives

```text
beta(z) K-d + mu(z) K-a = 0.
```

This is a vector identity in the entire odd kernel. It is stronger than the scalar cancellation that a Laurent/resolvent expansion would later recover.

### PROVED — canonical coupling-kernel specialization

For the actual even cubic coupling-kernel component, `beta` is exactly identified with its self-inner coefficient divided by the canonical shell norm. No one-dimensional-kernel claim is made.

### PROVED — even-regular odd-kernel response

If the even cubic coupling has a zero-shift preimage `A+ x+=b+`, the odd cubic coupling-kernel component is exactly

```text
sigma+ K-d + mu(u+0) K-a.
```

Thus the mixed even-regular / odd-resonant state has an exact finite source-driven kernel equation.

### PROVED — direct zero-shift cross-parity transfer

If both parity couplings have explicit zero-shift preimages:

```text
sigma- = alpha0 sigma+ + Gamma0 * mu(u+0)
Gamma0 = <u-0,g-> / rho-.
```

The proof works at zero itself. It does not use a zero-shift inverse, Moore–Penrose inverse, pseudoinverse, Laurent expansion, or resolvent limit.

### PROVED — whole-kernel product law

Under both preimage hypotheses:

```text
Gamma0 * mu(z) = 0
```

for every `z in ker A+`.

This is a compatibility law, not factorwise exclusion.

## What changed

Before #134 the project still had a real algebraic uncertainty at zero: the strongest cross-parity statements were shifted-resolvent theorems, while the kernel/source identities were only externally derived.

After #134, that uncertainty is gone. The direct zero-shift transport package is now compiled theorem authority.

Consequences:

1. a Laurent/pseudoinverse route is no longer needed to access the relevant kernel information;
2. the whole-kernel vector identity is the canonical zero-shift abstraction;
3. regular preimages are the correct local interface, not an invented zero-shift inverse;
4. the remaining bottleneck is not how information propagates across parity but whether the actual canonical source admits the sign required by a first-bad negative state.

## Upstream implications

### DERIVED — regular branch kills beta on the even kernel

If `A+ x+=b+` and `A+ z=0`, symmetry gives

```text
<b+,z> = <A+x+,z> = <x+,A+z> = 0,
```

so `beta(z)=0`.

Hence in the regular even branch the whole-kernel transport becomes

```text
A-(Dz)=mu(z)a
```

and the projected compatibility becomes purely source-driven.

This is already used inside the #134 proof chain; no new assumption is required.

### Do not introduce a zero-shift inverse abstraction

#134 demonstrates that the needed endpoint geometry is cleaner with explicit preimages plus kernel/range projection. Adding pseudoinverse/Laurent infrastructure now would increase dependency debt without adding stronger current information.

## Downstream implications

### Regular/regular branch

The theorem

```text
Gamma0 * mu(z)=0  for every z in ker A+
```

gives an exact dichotomy:

```text
Gamma0 = 0
or
mu annihilates the whole even predecessor kernel.
```

But exact generic countermodels already realize `Gamma=0`; therefore `Gamma0!=0` cannot be treated as structural. Likewise raw source-moment sign/nonvanishing is not a credible generic closure mechanism.

### Regular first-bad branch

Existing theorem authority already gives a negative endpoint:

```text
Re S0 < 0
Re sigma0 < 0
```

at the forced negative first-bad root in the regular branch.

The most direct remaining contradiction target is therefore an independent canonical theorem implying

```text
S0 >= 0
```

or equivalently a source-specific energy/coercivity inequality that forces the one-step extension to be nonnegative when the predecessor is nonnegative.

## Resurrected route — absolute canonical source energy

PR #131 decomposed the linear quadratic-normal source moment used by the parity defect. That observable deliberately annihilates scalar identity shifts.

For negative-root exclusion the project needs an observable that remembers the absolute spectral origin:

```text
E(v) = Re<Tv,v>.
```

This route is now ready because:

- the production pole/arch/prime source decomposition is theoremized (#131);
- the zero-shift trial/kernel geometry is theoremized (#124-#128);
- the direct zero-shift cross-parity transport is theoremized (#134).

The next theorem should expose the exact energy decomposition before attempting positivity.

## Recommended next theorem package — E4-A4b1

Candidate module:

```text
Zeta23/CCM/CanonicalSourceEnergy.lean
```

Candidate theorem layers:

1. define canonical parity energy `Re<Tv,v>` on the legal boundary-flat carrier;
2. expand through `canonicalSourceMatrix = pole - arch - prime`;
3. split the archimedean term into reduced diagonal, reduced off-diagonal and the scalar identity correction;
4. split the finite prime contribution into exact von-Mangoldt-weighted source-atom energies;
5. specialize to the canonical cubic shell `c`;
6. specialize to `cubicZeroShiftTrialVector`;
7. under `Ax0=b`, prove the exact regular energy identity
   ```text
   Re<Tu0,u0> = Re<Tc,c> - Re<Ax0,x0>
   ```
   in the repository's inner-product orientation;
8. connect this to the existing `S0` / `sigma0` endpoint theorem.

**Do not assert positivity merely because the decomposition exists.** A green E4-A4b1 decomposition is input to the next research pass, not branch exclusion.

## Decisive target — E4-A4b2 one-step domination

For either parity, with predecessor block `A>=0`, shell `c`, coupling `b=P_WTc`, and

```text
q_c = Re<Tc,c>,
```

the decisive target remains

```text
q_c >= 0
|<w,b>|^2 <= q_c Re<Aw,w>  for every w in W.
```

If proved from the actual canonical source:

```text
w in ker A -> <w,b>=0
```

so resonant coupling disappears. If `Ax0=b`, the same domination yields the zero-shift endpoint `S0>=0`, contradicting the already-proved `Re S0<0` at the forced negative root.

This is not a cheap helper theorem. It is essentially the one-step positivity theorem the project still has to earn from arithmetic normalization.

## Creative implication pass

### LEAD — source annihilation may characterize forbidden resonant kernels

The whole-kernel law suggests attacking the counterexample space rather than trying to prove generic `Gamma0!=0`.

A possible route is to characterize vectors in

```text
ker A+ ∩ ker(mu)
```

for the actual canonical source and show that the first-bad geometry cannot support the required coupling/kernel configuration.

This should be explored only if it spends genuinely canonical arithmetic information; generic linear algebra will be defeated by the existing structural countermodels.

### LEAD — high-order source-coordinate cancellation may feed coercivity

Boundary-flat moment constraints appear to suppress low-order source-atom energy terms:

```text
odd source-atom energy        first possible term: omega^7
even source-atom energy       first possible term: omega^9
even quadratic-normal moment  first possible term: omega^7
```

This remains **DERIVED / EXPERIMENTAL**. Its value is quantitative: it may provide small-coordinate bounds strong enough to dominate indefinite individual source atoms after the full canonical weighting is restored.

### LEAD — log-lift remains a branch simplifier, not closure

Dense regular-aperture selection could remove resonance from the chosen witness, but exact generic fixtures already show that positive-definite predecessors may coexist with a negative successor. Therefore log-lift is secondary to the energy theorem.

## Falsification checks

Any proposed energy/coercivity theorem must survive:

1. exact rational post-#129 countermodels;
2. the scalar-shift test — if the proof is unchanged under arbitrary `M+tI`, it cannot locate zero;
3. both parities;
4. low-dimensional canonical matrices;
5. exact elementary source atoms at `omega=1/2`, where legal vectors realize both energy signs;
6. the known canonical high-precision sample with negative raw source moment;
7. all existing firewalls: no D-isometry, no zero inverse, no factorwise division, no invented kernel dimension.

## Highest-leverage next moves

1. **Build E4-A4b1 exact absolute canonical source-energy decomposition.** Highest information gain because it exposes the true sign-bearing arithmetic object without assuming its sign.
2. **Adversarially test the resulting channel formula.** Search for low-dimensional canonical violations of `q_c>=0` and one-step domination before formalizing a large inequality proof.
3. **If the energy data supports it, attack E4-A4b2 canonical one-step domination.** This is the first route that can directly contradict the existing negative endpoint.
4. **Formalize omega^7/omega^9 endpoint cancellations only if they become a needed quantitative lemma for E4-A4b2.**
5. **Use log-lift regularization only if resonance remains the dominant proof obstruction after energy decomposition.**

## Standing questions after #134

> Given everything now formally true, what becomes possible that was not possible before?

Direct zero-shift source/kernel reasoning no longer needs an inverse or limiting procedure; the project can now attack the exact first-bad endpoint using the production source itself.

> If this contains a clue toward RH, where does it propagate?

The clue propagates from #131's canonical source decomposition through #134's exact zero-shift transport into the regular first-bad endpoint `S0/sigma0`, whose sign is already known to be negative at a hypothetical off-line-zero witness.

> What experiment, lemma or reformulation most efficiently tests whether the clue is real?

Expose the exact absolute source-energy decomposition and immediately test the one-step domination inequality on low-dimensional canonical matrices before investing in a global formal proof.

**RH remains OPEN.**

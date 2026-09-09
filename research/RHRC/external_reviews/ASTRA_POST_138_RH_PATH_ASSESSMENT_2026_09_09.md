# Astra external research review — post-#138 RH path assessment

Date: 2026-09-09

> **Authority firewall:** this is an external research review preserved for provenance. It is not Lean theorem authority, machine claim promotion, or RH evidence. **RH remains OPEN.**

## Audited repository state

Astra reports auditing merged `main` at:

```text
main = ebf289bdfdde69020bee0d1571047f155e5de4db
tree = d26cd83709437260d0a16630d90c73a93f64c975
PR #138 = merged
latest theorem increment = PR #137
```

The review reconstructs the project from approximately PR #132 through #138, with emphasis on #134, #136 and #137.

## Principal conclusion

The #137 one-step determinant is a precise coordinate system for the missing positivity but not, by itself, a cheaper positivity theorem. Under predecessor nonnegativity and the one-dimensional-shell decomposition, the universal certificate

```text
q_c >= 0
forall w, Delta(w) >= 0
```

is assessed as equivalent to positivity of the successor quadratic form.

The review therefore recommends moving **regular-aperture/log-lift selection** ahead of universal domination. The proposed reduction is:

```text
off-line zero
  -> finite canonical negative witness
  -> nearby aperture preserving negativity
  -> both predecessor parity blocks positive definite
  -> reselect first-bad
  -> unique regular trial u0 = c - A^-1 b
  -> Ecanonical(u0) = Re S0 < 0
  -> independent arithmetic proof Ecanonical(u0) >= 0
  -> contradiction.
```

The regular-selection step does not prove positivity and is therefore viewed as a genuine reduction rather than a restatement of RH.

## Key derived observations reported

These are not newly compiled Lean theorems.

1. For `k = P_(ker A)b`,

   ```text
   Delta(k) = -||k||^4.
   ```

   Thus resonance itself selects an explicit negative determinant witness.

2. The two odd predecessor correction vectors are reported to satisfy

   ```text
   d = -(6/(2*N-1)) a,
   ```

   checked by exact rational arithmetic for `K=2,...,30` and supported by an elementary power-sum derivation.

3. At a safe negative explicit root `lambda`, with

   ```text
   w_lambda = (A-lambda I)^-1 b,
   r_lambda = q_A(w_lambda),
   n_lambda = ||w_lambda||^2,
   ```

   the review derives

   ```text
   Delta(w_lambda)
     = lambda*r_lambda*(rho+n_lambda)
       - lambda^2*n_lambda^2.
   ```

4. For a differentiable regular family with minimizing trial `u0 = c - A^-1 b`,

   ```text
   dS0/dt = <u0, M'(t)u0>.
   ```

   This gives an exact sensitivity observable for prime-weight perturbations.

## Log-lift lead

The recommended next theorem attempts to freeze the finite prime cutoff and expose

```text
M_Q(L) = -log(L) I + B_Q(L).
```

With `L = exp z`, the remainder should become periodic under `z -> z + 2*pi*i`. If the compressed determinant vanished identically, periodicity would force one fixed finite-dimensional characteristic polynomial to have too many distinct roots.

The review explicitly lists the missing obligations:

- exact scalar coefficient after compression;
- frozen-cutoff analyticity;
- physical cutoff-threshold continuity;
- fixed-basis/Gram correctness;
- simultaneous avoidance across finitely many sizes and both parities;
- continuity preservation of the negative witness;
- fresh first-bad reselection after moving the aperture;
- exact identification of the projected predecessor compression.

## Falsification findings reported

### Atomwise determinant/SOS route

The review reports a negative first nonzero two-vector determinant coefficient for an elementary source atom. For tested predecessor/shell fixtures, the first determinant orders are `omega^18` in odd parity and `omega^22` in even parity.

Research consequence: the old `omega^7 / omega^9` cancellation signal does not support a positive **atom-by-atom** determinant proof. Full-source cancellation remains open.

### Canonical cancellation conditioning

The review reports an even canonical case at `L=3, K=6` with

```text
S0 ~= 4.91225958747865e-10
```

and a ratio of summed absolute channel magnitudes to the final endpoint of approximately

```text
6.4583e20.
```

This is high-precision numerical evidence, not interval-certified theorem evidence.

### Prime-coefficient sensitivity

The review reports that at `L=2, K=3`, a relative `1e-8` change to the prime-2 coefficient can flip one successor negative while both predecessors and the shell energy remain positive. A consistent change to the available powers `2,4` produces the same qualitative behavior.

These are modified sources, not canonical zeta counterexamples. They show that an eventual proof must use the exact arithmetic coefficients, not merely positive weights/finite support/parity/channel structure.

## Ranked next research moves from the review

1. Prove nearby-aperture simultaneous predecessor injectivity/positive definiteness and reselect the first-bad witness.
2. Preserve pole-neutrality through finite approximation as an alternative carrier-reduction route.
3. Search for an independent paired-channel bound on the regular Schur energy.
4. Prove shell positivity only if a concrete source inequality survives falsification.
5. Formalize correction-vector proportionality as a cleanup theorem.
6. Formalize the root-selected determinant witness as a precise discovery interface.

## Closing assessment from the review

The smallest unresolved observable after a successful regular-aperture reduction is one scalar canonical Schur energy on the minimizing trial. The review found no established arithmetic proof of its nonnegativity.

The research value is therefore a **rerouting and obstruction compression**, not an RH proof.

**RH remains OPEN.**
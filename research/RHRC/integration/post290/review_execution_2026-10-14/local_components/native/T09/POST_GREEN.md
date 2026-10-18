# T09 actual mixed Weil response: frozen local result

## What became formally true

`Zeta23/CCM/NativeWeilResponse.lean` is exact local GREEN at SHA256
`0ebc3954a20596f32b92f1a9f6b96f959ea5e9758d639b3eaea298cb072ff377`.
Pinned Lean 4.33.0-rc2 exited zero with unchanged source bytes. All 17
printed public theorem roots use only `propext`, `Classical.choice`, and
`Quot.sound`. The local receipt records source and evidence hashes; the
integration commit and remote CI remain parent-owned.

The actual response is Arch(f)+Pole(f)-Prime(f), with the literal repository
gamma bracket, actual prime coefficients, both translated prime histories,
and both elementary pole terms. It satisfies the exact mixed identity
`zetaZeroConfig.W f v = integral (Response(f) * conj(v))`. The source needs
compact C2 regularity; the second test needs only continuity and compact
support. There is no caller explicit-formula bridge premise. The proof
uses the existing unconditional actual mixed Weil literature dictionary.

The response is continuous and its restriction, or zero-extended restriction,
to every compact interval belongs to L2. Separately, both the literal
Archimedean Fourier multiplier and the actual full-line inverse-integral
Archimedean response belong to L2. Thus the required compact-C4 global Arch
claim follows from a stronger compact-C2 theorem. This global result is not
inferred from compact-interval membership.

## Proof and conventions

One common integer cutoff is chosen uniformly over each bounded physical
interval before sum/integral exchange. It retains both x-log(n) and
x+log(n) histories. The prime mixed pairing has exactly one copy of each
correlation. The pole mixed pairing uses opposite imaginary Fourier
arguments and the conjugated second test. The total integral is split only
after continuity plus compact support supplies each integrability premise.

The Arch integral is continuous by its actual L1 Fourier multiplier. Its
multiplier L2 proof combines the source C2 Fourier bound with the native
quadratic gamma bound and actual multiplier L1 integrability. For global
response L2, the proof identifies the classical L1 Fourier integral with
the actual L2 Fourier transform almost everywhere, by compact smooth test
duality and the L2 tempered-distribution theorem. It then applies the exact
physical frequency rescaling and 1/(2*pi) normalization. This pays the
missing inverse-transform bridge explicitly.

## Workflow harvest

The exact local compiler is a FORMAL VALIDITY GATE: all 17 roots pass with
the permitted axioms. The typed consumer captures all public definitions,
full theorem binders, and explicit mixed-pairing/local-L2/global-L2 terms.
The promoted proof-escape gate passes over 642 files. The supplementary
ordinary and optimized Python convention regressions each pass three tests:
nonreal mixed orientation, both prime shifts, opposite pole arguments, and
the plus-forward/minus-inverse Fourier normalization. These regressions
carry no continuous-transform or RH theorem authority. Remote workflow
harvest and the final Bounds direct consumer are integration-owned.

## What changed and implications

The earlier five-root checkpoint supplied Arch and pole pairings. The
sixteen-root checkpoint added the actual finite prime history, exact total
pairing and local response L2. The final seventeenth root closes global
Arch L2 without introducing any new premise. The sixteen-root source and
its successful log remain preserved as a recoverable checkpoint.

Upstream, compact C2 is sufficient throughout these exports, so callers
with C4 data can use the stronger theorem directly. The L1/L2 Fourier
identification helper is generic but private; no public duplicate is
needed for current consumers. Downstream, the exact mixed identity pays
the dictionary needed by the finite-aperture H1 bound and physical forcing
projection. Those consumers can now use actual source response integrals
without a caller bridge.

The earlier inverse-integral gap is eliminated. Exact original detector
forcing and its two distinct Schur records remain separate subsequent
tasks; none was started during the final freeze. The finite-aperture
estimate does not establish any closing subexponential estimate.

## Leads, falsification and remaining questions

DERIVED: the literal compact-interval response is now a legitimate L2 input
to the actual physical projection. LEAD: composing this exact dictionary
with original detector histories should reduce forcing comparison to
explicit local response estimates. Fast falsification checks are conjugate
orientation on nonreal mixed tests, deletion of either prime history,
incorrect pole arguments, or a lost 2*pi rescaling. The convention tests
exercise those mutations, while Lean proves the universal identities.

The highest-leverage next mathematical task is the exact original-source
forcing identity with its measured projection error and both distinct
Schur interfaces, once its prerequisites and integration are fully green.
No implication here establishes all-damped X L2, all-damped Y range closure,
or the required closing Schur asymptotic. A-X, B-Y, C-Schur and RH remain
OPEN. Given the new literal response dictionary, the next question is
whether the original finite trial's forcing can be bounded at the needed
rate without replacing the actual source or assuming that rate.

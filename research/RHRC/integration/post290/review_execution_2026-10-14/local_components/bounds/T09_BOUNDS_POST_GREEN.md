# T09 bounds: post-green research pass, 2026-10-14

## What became formally true

`NativeWeilResponseBounds.lean` proves the actual native Weil form estimate on the physical support `[0,L]` for every `L >= 0` and every pair of complex compact C2 tests:

`norm (zetaZeroConfig.W f v) <= C_Q (1+L) exp(L/2) H1(f) H1(v)`.

One positive constant works for all L and both tests. It is constructed as `C_A + 6`, where `C_A` is obtained from the proved native gamma-bracket growth theorem. The exact norm is `originalDetectorPhysicalH1Error f 0`. Neither a generic explicit-formula premise, a caller-supplied operator bound, a zero, nor an RH hypothesis is accepted.

The exact compiler run and all 21 printed public roots have only `propext`, `Classical.choice`, and `Quot.sound`. The receipt records source and log hashes. This is local pinned-compiler evidence; it is not a hosted CI result or a claim that the entire 22-task build is complete.

## Workflow harvest

The module was checked with the pinned Lean 4.33.0-rc2 driver and the existing pinned Mathlib cache. Its final direct consumer checks the literal C2 `[0,L]` statement. No workflow was dispatched, no D2 child was retried, and no historical research disposition was altered by this task. The companion native response checkpoint supplies the exact mixed pairing and channel continuity; its separate receipt owns that evidence.

## What changed

The bound is now a theorem about the literal native source form, including both translated-prime channels and both elementary-pole terms. The channels cost respectively `C_A`, `4(1+L)exp(L/2)`, and `2L exp(L/2)` times the two H1 norms. Their sum gives the required `C_A+6` constant.

The proof retains the prescribed C2 class. It does not assume that the derivative of a C2 test is itself C2. Instead, compact-autocorrelation inversion proves Parseval whenever the Fourier square is integrable. Existing C2 Fourier decay establishes the required weighted-square integrability for the test and the Fourier-square integrability of its first derivative. The exact paper convention gives the energy factor `2*pi`, which cancels the Archimedean prefactor.

## Upstream implications

PROVED: compact-autocorrelation Parseval is available for any continuous compact source with integrable Fourier square. The C2 H1 energy identity is an application. This removes the earlier proof-engineering obstruction around applying a C2 inversion theorem directly to a merely C1 derivative.

PROVED: the finite arithmetic mass estimate follows from `Lambda(n) <= log(n)` and the telescoping inequality `1/sqrt(n) <= 2(sqrt(n)-sqrt(n-1))`; it requires no prime-number theorem or numerical certificate.

## Downstream implications

DERIVED: T11 can combine this source-independent constant with the actual finite-mode H1 bound to pay the projected native forcing error. The eta contribution remains explicit. Together with trial depth, the same theorem supplies the prescribed finite-aperture eta bound. Those downstream theorem declarations remain the responsibility of the forcing task.

## Resurrected routes

The physical C2 bilinear route no longer needs an extra smoothing approximation or a stronger C3/C4 caller assumption merely to justify derivative Parseval. Global Archimedean L2 membership is a distinct companion-module issue; the present bound does not substitute compact-interval membership for it.

## New RH-relevant clues

LEAD / HYPOTHESIS: useful arithmetic cancellation or additional structure would need to improve the finite prime mass estimate in the particular selected states. The current theorem provides a rigorous baseline against which any such improvement can be stated and falsified.

OPEN: the bound grows as `(1+L)exp(L/2)`. It is not a subexponential closing law and does not establish A-X, B-Y, C-Schur, or RH.

## Falsification checks

The proofs quantify over all complex pairs, rather than only diagonal or real tests, and consume the exact mixed pairing with the source in the linear slot. Both prime shifts are retained. The finite arithmetic proof includes N=0, and the common-support theorem includes L=0. Pole terms are bounded without assuming neutrality. The Fourier derivative uses the actual `-i*xi` paper convention and the energy identity retains the exact `2*pi` normalization. All these obligations are theorem-level, rather than finite-grid tests.

## Highest-leverage next moves and outstanding questions

1. Consume this constant in the same-state physical projection and forcing theorem, retaining the eta term.
2. Complete the companion global Archimedean L2 bridge if it is not already covered by a later exact receipt.
3. Revisit whether the actual selected source has cancellation beyond the universal exponential arithmetic mass bound. The current proof supplies no such improvement.
4. Keep the distinction between this finite-aperture estimate and every OPEN terminal premise visible in final serialization and semantic review.

There is no remaining mathematical gap in the owned H1 bilinear estimate. The larger producer, final receipt integration, semantic signoff, and closing laws are separate obligations.

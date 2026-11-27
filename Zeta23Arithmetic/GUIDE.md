# Guide to the compact edition

The proof is Levent Alpöge's, with Claude. This project is a shorter rewriting of Levent Alpöge's Lean proof (see <https://alpo.ge/remark.pdf>). It follows that proof's method; many steps are proved by other arguments, and parts of it, mostly background material, were ported from there and then rewritten.

## 1. The theorem, and what to read to trust it
`New.grh` states that L(s, χ) ≠ 0 for re s > 1/2 and every Dirichlet character χ, the pole s = 1 of principal χ excepted. The functional equation gives RH and GRH for Dirichlet L-functions. To trust this, read `src/Statements.lean` (it imports only Mathlib), the five theorems of `src/Main.lean`, and, after a build, their `#print axioms` output (expected: `propext`, `Classical.choice`, `Quot.sound`). One trusts Lean's kernel and Mathlib's definitions of ζ and L. Lean checks neither comments nor this guide.

## 2. Folders and reading order
The three main theorems are A, short forms (`Data.short_forms`, in Endgame/ShortAndEnough), B, enough forms (`Data.enough_forms`, same file), and C, integral forms are long (`Data.integral_forms_long`, in Endgame/LongForms). The main inequality `star_inequality`, in `src/New/Main.lean`, combines them; a comment near the top of that file lists the inputs. Short and long refer to the norms and the covolume of theta lifts.

Read `src/New` in this order: Main; Endgame; then the definitions in Data, Seesaw/IndexTypes and Trace/GoodIdempotent. The other folders serve mainly A (Curve, Columns, TwistedHecke, Core, Seesaw), B (Filling, RealPlace, DiscreteSeries) and C (Heights, Rows, Exchange, Trace, GaloisRep, Forms, SiegelWeil, Weil; for the twists, Selmer, Patching and Lift). `src/Lib` proves background missing from Mathlib, in the forms needed here. It ranges from class field theory to Galois representations of eigenforms (`sphericalCompat_std`).

## 3. Letters (`P : Parameters`, `D : Data P`; x → ∞)
|letter|meaning|
|-|-|
|N₀, d|18480 ∣ N₀; d a prime ≡ N₀/2−1 mod N₀ (`Parameters`)|
|E, f|E = K(ζ), K = ℚ(√−d); tops are the infinite places ≡ 1 mod N₀; ζ has order N₁, N₀ ∣ N₁; f = φ(N₀)·#tops infinite places, #tops ≈ x¹¹; rd_E the root discriminant of E|
|x, x₁, b|scales; the error term `primeError` is bounded above at x; (log b)¹⁰⁰ ≤ x, x^(10⁶) ≤ x₁, x₁^(10⁶) ≤ b|
|m|number of theta lifts, in [√x, 2√x]|
|k, r, t|k, r the ranks of columns and rows; r = k+m−1 ≈ x⁵; t = 5r (not the finite set `t` in the Lean statements of A and B)|
|a|least multiple of N₁ that is at least xb; `Data.primeSum` runs up to a|
|N, g|levels: the prime N; g = g₀g₁ ≤ b²², below the places v of 𝖦 = ∏_v GL_r(𝔽_v); rows have level g only|
|ϑ|weight-0 character of U(1), tame, conductor prime to gN (`Data.Twist`); in the chain Θ_ϑ (`Data.Θ`) also ϑ², …, ϑ^m have that conductor (`Data.MFoldTwist`)|
|row, column|rows: good forms on an indefinite U(r) (`Data.rows`); columns: algebraic forms on a definite U(k) (`Data.Column`); in Selmer also Galois representations (`IsRow`, `IsColumn`)|

# T01 actual physical completed-input zero jet

## What became formally true

The checked new source is `Zeta23/ExceptionalZero/NativeActualInputZeroJets.lean`,
SHA256 `04a808f91da07d2c5cb9109bb899f50996f8e21aa9bbb3b14289edd7252f9d7d`.
The parent intake verified baseline commit
`efa6ceea7bba2b34ff453a70a32a0800fee98b82`, tree
`511f6dc182d9a02b54e9404e93c32eb614fbff34`. This is local component compiler
evidence on the changed source, not a claim that this new source was already
part of that baseline Git tree or checked by remote CI.

The actual causal-L2 completed input has its literal damped Laplace transform.
On a genuine neighborhood of the witness parameter, it equals the existing
single-source expression `-(R*J)*zeta'`. At an actual zero of multiplicity m,
its order is m-1. The constructed actual causal witness has physical pairing
`(-1)^m R(p) J(p) zeta^(m)(rhoR)`, which is nonzero. The selected zero rhoR is
the original zero or its functional-equation reflection, preserving actual
multiplicity while allowing strictly positive damping and witness real part.

Consequently the actual completed input is outside the closure of the range
of the actual causal completion operator at that damping. No kernel moment,
input jet, source visibility, source L2 membership or range conclusion is an
extra caller premise. Every finite adjoint residual iterate preserves that
same nonzero physical pairing and has an explicit positive norm lower bound.

All eight printed public theorem roots use only `propext`, `Classical.choice`
and `Quot.sound`. The exact local compiler exited zero with source bytes
unchanged. The first attempt had one exponent-rewrite failure; the checked
source fixes only that proof calculation. No statement was weakened.

## Workflow harvest

The local pinned compiler is the formal-validity gate. The existing promoted
proof-escape scan passed on 630 source files, including the new source. Exact
finite convention regressions passed in ordinary Python and under `python -O`:
multiplicities 1, 2 and 3, phase, iterated-derivative factorial convention,
`p=w+epsilon`, conjugate-linear first slot, single source factor and the
exceptional zeta-pole cancellation guard. These finite tests supplement the
universal Lean theorem; they create no independent analytic authority.

No new GitHub workflow was dispatched by this task. Remote CI and the final
global output-contract/bindings checks belong to parent integration and are
not silently counted as passed here. T02 is the direct mathematical consumer;
its result is recorded separately when checked.

## What changed and what it permits

Previously the actual kernel annihilation and an analytic-expression input
jet were separately proved, but their physical input composition was still
open. This module closes exactly that composition, paying neighborhood
equality before transferring derivatives or analytic order. The old obstacle
is eliminated without requiring simple zeros: the highest useful witness
degree is m-1 because the actual input uses zeta'.

Upstream, the already proved source visibility, actual transforms and
functional-equation reflection suffice; no stronger source estimate is
required for this obstruction. Downstream, the explicit B-Y range condition
can now imply Mathlib's exact RH statement by contradiction, and A-X can feed
that condition through the already proved literal a*X=Y operator bridge.
Those are conditional sufficiency statements, not proofs of either closing
condition. No reverse B-Y-to-A-X implication is claimed.

## Clues and falsification

PROVED: under an actual off-line zero, finite residual descent cannot drive
the actual input residual norm to zero because a fixed nonzero adjoint-kernel
pairing survives every iteration. A monotone decreasing residual norm alone
therefore cannot supply B-Y or the missing convergence-to-zero conclusion.

LEAD: an independent argument forcing the actual input orthogonal to this
specific adjoint kernel would directly confront the obstruction. This file
does not supply such an argument and does not assert that an arbitrary
causal stable input has that property. The fastest falsification is the
proved positive residual lower bound itself whenever an off-line zero is
assumed; any proposed unconditional convergence argument must account for it.

The boundary point p=1/2 is excluded using the actual zero's nontriviality.
The actual kernel transform there has the separately proved residue value
1/2; substituting totalized zeta products would give the wrong result.

## Highest-leverage next move

Complete T02's requested conditional A-X/B-Y wrappers and prove the original
half-line integral condition equivalent to literal full-line source L2
membership. RH, A-X, B-Y and the independent C-Schur closing condition remain
OPEN. This task introduces no fourth terminal criterion.

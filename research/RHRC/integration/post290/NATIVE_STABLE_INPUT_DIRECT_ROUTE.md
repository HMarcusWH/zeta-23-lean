# Direct ordinary-L2 route for the actual integer-drive input

Status: **LEAD / formal construction OPEN**. This changes neither the fixed
source nor the integer/prime coefficients. It does not control X, remove the
native range obstruction, or discharge the final producer.

The strongest paper bound on the actual U is super-exponential. The core
ordinary damped-L2 input statement appears to need less. For the literal
j=P²q, compact C-infinity support gives finite weighted L1 norms of j and j'.
The double elementary zero of its actual transform gives

integral exp(-u/2) j(u) du = 0,
integral u exp(-u/2) j(u) du = 0.

The first identity is covered by the new compact-potential candidate; the
weighted first moment still needs its exact Fourier-derivative or integration
by parts proof. Neither identity is supplied as a new producer premise.

For physical time t define the real function on positive x

F_t(x) = log(x) / sqrt(x) * j(t-log(x)),

and extend it by zero at nonpositive x. Its exact support lies in
[exp(t-s),exp(t+s)], which is separated from zero. Its integer samples are
the unchanged actual U, including the n=1 zero coefficient. Log substitution
and the two moments give integral F_t(x) dx = 0.

Abel summation with the literal floor counting function, together with
integration by parts and zero endpoint terms outside the support, gives

abs(sum_{n>=1} F_t(n) - integral F_t(x) dx) <= integral abs(F_t'(x)) dx.

No prime-counting hypothesis is used here. The derivative on x>0 is exactly

x^(-3/2) * ((1-log(x)/2)*j(t-log(x)) - log(x)*j'(t-log(x))).

A second log substitution yields, for t>=0,

abs(U(t)) <= C_j * (1+t+s) * exp(-t/2),

where one valid finite constant is

C_j = integral exp(u/2) * (abs(j(u)) + abs(j'(u))) du.

The integrals retain their true compact support. The extension's derivative
at zero must be justified from its actual support gap, not by differentiating
log or sqrt at zero.

For the actual causal c=-exp(-v/2)+2exp(-3v/2), one has
abs(c(v))<=3exp(-v/2) for v>=0. The actual source's pre-prime zero history
puts U before zero identically at zero. Thus the literal causal Y=c*U obeys

abs(Y(t)) <= 3*C_j*exp(-t/2)*((1+s)*t+t^2/2), t>=0,

and vanishes before zero. This would prove Y_epsilon in ordinary L2 for
every epsilon>=0, independently of X membership or stable inversion.
It does not prove the paper's stronger weighted tail exponent 3/2. If the
exact formal consumer requires that stronger domain, this weaker estimate
cannot substitute for it.

Required formal bridges are the actual weighted first moment, smooth/compact
positive-x extension, floor Abel-summation identity with exact finite
history, both justified log substitutions, and actual causal-convolution
integrability. The already proved pointwise N*X=U and c*N=a do not themselves
supply the global identity a*X=Y; that identity still needs its legal
locally finite causal Fubini argument before any global L2 assumption on X.

Fast falsification checks: replace j by a compact source with a nonzero
elementary moment (the uncancelled continuum term grows as exp(t/2)); omit
the weighted first moment (a polynomial-times-exp(t/2) term remains); inspect
n=1, entering-integer endpoints, t near zero, the source support boundaries,
and time versus aperture t=2a. Do not replace the actual signed j by abs(j)
inside either cancellation identity. Large constants at scale 1/4096 are
permitted for membership but provide no useful uniform detector time.

Highest-leverage next move: prove the single exact compact-source Abel
discrepancy lemma and fill its two moments from the literal j. This may close
the ordinary stable-input prerequisite with fewer dependencies than the full
super-exponential Poisson estimate, while preserving the native range defect.
M19, range jets, the full mandatory output and RH remain **OPEN**.

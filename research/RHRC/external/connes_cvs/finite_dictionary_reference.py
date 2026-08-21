#!/usr/bin/env python3
"""Reference-only finite Guinand--Weil dictionary implementation.

Adapted from:
  HMarcusWH/connes-cvs-
  commit 5a66d0cd177ef8b8ad1c2c93165b8d56ca40292c
  papers/2_guinand_weil_dictionary_tail_order/scripts/verify_dictionary_threeroute.py
  source blob 90576ea92835fff2f9dd2e3aa63ad99829bd17e5

Original software is MIT licensed; see the LICENSE file in this directory.

AUTHORITY BOUNDARY
------------------
This file is a numerical/reference oracle only. It must never enter the Lean
import graph and cannot promote an RHRC mathematical claim.

It preserves the finite dictionary chain used by the source verification code:

    v -> symmetric centered coefficients u
      -> trigonometric polynomial T_v
      -> Volterra kernel K_v
      -> compact Fourier-side weight ghat_v
      -> entire test transform g_v.

The zero-side and archimedean-tail routines from the upstream three-route script
are deliberately omitted here: PR #35 uses this module only to regression-test
the finite dictionary objects and transform convention.

Precision is caller-owned: importing this module never mutates mpmath's global
working precision.  The reference construction is defined only for the paper's
positive-aperture domain c > 1 and for a coefficient vector of exactly N+1
entries.
"""

import mpmath as mp


class TestFn:
    """Finite dictionary test function in the pinned Groskin convention."""

    def __init__(self, c, N, v):
        if not isinstance(N, int) or isinstance(N, bool) or N < 0:
            raise ValueError("N must be a nonnegative integer")

        values = list(v)
        if len(values) != N + 1:
            raise ValueError(
                f"coefficient vector must have exactly N+1={N + 1} entries; "
                f"got {len(values)}"
            )

        c_mp = mp.mpf(c)
        if not c_mp > 1:
            raise ValueError("c must satisfy c > 1 so L=log(c) is a positive aperture")

        self.c = c_mp
        self.N = N
        self.L = mp.log(c_mp)
        self.Delta = self.L / (2 * mp.pi)
        self.v = [mp.mpf(x) for x in values]

        u = {0: self.v[0]}
        for k in range(1, N + 1):
            u[k] = self.v[k] / mp.sqrt(2)
            u[-k] = self.v[k] / mp.sqrt(2)
        self.u = u

        # Closed-form coefficients for
        # K_v(w) = sum_k (alpha_k + beta_k*w) exp(2*pi*i*k*w).
        self.alpha = {}
        self.beta = {}
        for k in range(-N, N + 1):
            s = mp.fsum(u[n] / (k - n) for n in u if n != k)
            self.alpha[k] = 2 * u[k] * s / (mp.pi * 1j)
            self.beta[k] = 2 * u[k] ** 2

    def T(self, t):
        """T_v(t) = sum_m u_m exp(2*pi*i*m*t)."""
        return mp.fsum(
            self.u[m] * mp.exp(2j * mp.pi * m * t) for m in self.u
        )

    def K(self, w):
        """Closed-form Volterra kernel K_v(w)."""
        return mp.re(
            mp.fsum(
                (self.alpha[k] + self.beta[k] * w)
                * mp.exp(2j * mp.pi * k * w)
                for k in self.u
            )
        )

    def K_quad(self, w):
        """Independent integral definition: 2 int_0^w T(t)T(w-t) dt."""
        return mp.re(2 * mp.quad(lambda t: self.T(t) * self.T(w - t), [0, w]))

    def ghat(self, xi):
        """Compact Fourier-side weight in the Groskin convention."""
        ax = abs(xi)
        if ax > self.Delta:
            return mp.mpf(0)
        return mp.pi * self.K(1 - ax / self.Delta)

    @staticmethod
    def _int_poly_exp(al, be, a):
        """Integral_0^1 (al + be*w) exp(i*a*w) dw, complex a allowed."""
        if abs(a) < mp.mpf(10) ** -8:
            tot_a = mp.mpc(0)
            tot_b = mp.mpc(0)
            for j in range(25):
                cj = (1j * a) ** j
                tot_a += cj / mp.factorial(j + 1)
                tot_b += cj / mp.factorial(j) * (mp.mpf(1) / (j + 2))
            return al * tot_a + be * tot_b
        ia = 1j * a
        e = mp.exp(ia)
        return al * (e - 1) / ia + be * ((e * (ia - 1) + 1) / (ia ** 2))

    def g(self, z):
        """Exact finite closed form for g_v(z)."""
        z = mp.mpc(z)
        th = z * self.L
        tot = mp.mpc(0)
        for k in self.u:
            al, be = self.alpha[k], self.beta[k]
            tot += (
                mp.exp(1j * th)
                / 2
                * self._int_poly_exp(al, be, 2 * mp.pi * k - th)
            )
            tot += (
                mp.exp(-1j * th)
                / 2
                * self._int_poly_exp(al, be, 2 * mp.pi * k + th)
            )
        val = 2 * mp.pi * self.Delta * tot
        # On the real axis the exact transform is real by evenness.  Away from
        # the real axis preserve the full complex value so the oracle remains
        # holomorphic and can expose complex-normalization errors.
        return mp.re(val) if mp.im(z) == 0 else val

    def g_quad(self, r):
        """Physical-space representation used to lock the paperFT convention."""
        return mp.quad(lambda y: self.K(1 - y / self.L) * mp.cos(r * y), [0, self.L])


def regression_guards(c, N, v):
    """Return independent closed-form-vs-integral residuals for K and g."""
    tf = TestFn(c, N, v)
    k_residual = max(
        abs(tf.K(mp.mpf(w)) - tf.K_quad(mp.mpf(w))) for w in ("0.3", "0.77")
    )
    g_residual = max(
        abs(tf.g(mp.mpf(r)) - tf.g_quad(mp.mpf(r))) for r in ("0.9", "14.2")
    )
    return {
        "K_closed_vs_quad": k_residual,
        "g_closed_vs_quad": g_residual,
    }


if __name__ == "__main__":
    # Match the source script's historical working precision only for the
    # standalone smoke test; importing the module never changes caller state.
    with mp.workdps(40):
        result = regression_guards(13, 4, [1, 2, -1, 3, 2])
        for key, value in result.items():
            print(f"{key}: {mp.nstr(value, 8)}")

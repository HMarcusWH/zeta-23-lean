"""R002-A masking diagnostic (FINITE NUMERICAL DIAGNOSTIC ONLY).

Builds the windowed zero-side Gram
    G_kl = sum_rho m_rho * phihat(gamma_rho - tau_k) * phihat(gamma_rho - tau_l)
for a synthetic zero set (on-line bulk at mean spacing 2*pi/l, plus one
off-line pair at depth delta), with flat taper phi = 1 on [-L/2, L/2]:
    phihat(r) = 2 sin(rL/2)/r,        phihat(r - i d) = complex
and tests the predicted visibility condition

    lambda_min(Ghat) < 0   <=>   delta * L  >~ const.

Predictions being tested (derived by hand):
  ||y||^2 ~ delta^2 * L^4/12         (signal direction norm, small delta)
  signal (hat units)  ~ m delta^2 L^2 / 6
  masking (hat units) ~ 1/lambda = l/L
  => visibility iff  delta^2 L^2 * lambda >~ 6   i.e.  delta*L >~ sqrt(6/lambda)
"""
import numpy as np


def phihat(z, L):
    """paperFT of flat taper 1_{[-L/2,L/2]}: 2 sin(zL/2)/z, complex z, z=0 -> L."""
    z = np.asarray(z, dtype=complex)
    out = np.empty_like(z)
    small = np.abs(z) < 1e-12
    out[small] = L
    zz = z[~small]
    out[~small] = 2 * np.sin(zz * L / 2) / zz
    return out


def build_gram(L, l, T, halfwidth, delta, gamma_off, m_off=1, seed=0):
    """Grid tau_k = T + 2 pi k / L over [T-halfwidth, T+halfwidth];
    on-line zeros at mean spacing 2 pi / l (deterministic lattice + jitter)."""
    rng = np.random.default_rng(seed)
    h = 2 * np.pi / L
    ks = np.arange(-int(halfwidth / h), int(halfwidth / h) + 1)
    tau = T + ks * h
    d = len(tau)

    # on-line zeros over a padded range (bandwidth of phihat ~ decays like 1/r)
    pad = 40 * h
    spacing = 2 * np.pi / l
    gam = np.arange(T - halfwidth - pad, T + halfwidth + pad, spacing)
    gam = gam + rng.uniform(-0.15, 0.15, size=gam.shape) * spacing

    G = np.zeros((d, d))
    for g in gam:
        u = phihat(g - tau, L).real  # on-line: gamma_rho real => u real
        G += np.outer(u, u)

    # off-line pair at gamma_off, depth delta: gamma_rho = gamma_off - i*delta
    if delta > 0:
        u = phihat((gamma_off - tau) - 1j * delta, L)
        x, y = u.real, u.imag
        G += 2 * m_off * (np.outer(x, x) - np.outer(y, y))
    return G, tau, d


def main():
    print("R002-A masking diagnostic: does lambda_min(G) < 0 track delta*L ?\n")
    print(f"{'lam':>5} {'L':>7} {'l':>6} {'delta':>9} {'delta*L':>8} "
          f"{'lam_min_hat':>12} {'neg?':>5}")
    l = 12.0          # l = log(T/2pi); T ~ e^12 ~ 1.6e5
    T = np.exp(l) * 2 * np.pi
    for lam in [0.5, 1.0, 2.0]:
        L = lam * l
        for delta in [0.0, 0.01, 0.03, 0.06, 0.1, 0.2, 0.4]:
            G, tau, d = build_gram(L, l, T, halfwidth=25 * 2 * np.pi / L,
                                   delta=delta, gamma_off=T)
            a = 1.0                       # flat taper: a = L^-1 int phi^2 = 1
            Ghat = G / (a * L ** 2)
            ev = np.linalg.eigvalsh(Ghat)
            lm = ev.min()
            print(f"{lam:5.1f} {L:7.2f} {l:6.1f} {delta:9.3f} {delta*L:8.2f} "
                  f"{lm:12.5f} {'YES' if lm < -1e-9 else '.':>5}")
        print()

    print("Predicted threshold delta*L ~ sqrt(6/lambda):",
          {lam: round(float(np.sqrt(6 / lam)), 2) for lam in [0.5, 1.0, 2.0]})


if __name__ == '__main__':
    main()

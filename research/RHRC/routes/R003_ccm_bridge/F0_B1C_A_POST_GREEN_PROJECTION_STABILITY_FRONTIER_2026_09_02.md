# F0-B1C-A post-green settlement — projection-stability frontier

**Date:** 2026-09-02  
**Route:** R003 / CCM finite obstruction  
**Claim firewall:** RH remains OPEN.

## Exact authority

Permanent merged main after PR #91:

~~~text
main = bab94aed54298de6fc6676808a0b0e46c2db6046
tree = f98b3051ca789ef0d134934fc01d97ac7497d4ca
merged through = PR #91
~~~

PR #91 final hardened theorem head:

~~~text
head = cf1c9b6536264deb8773fa8b0bb3650b07fcff40
head tree = f98b3051ca789ef0d134934fc01d97ac7497d4ca
merge = bab94aed54298de6fc6676808a0b0e46c2db6046
RHRC #660 = SUCCESS
Permansson #433 = SUCCESS
~~~

The final PR tree is exactly the permanent merge tree.

The production theorem

~~~text
Zeta23.CCM.exists_localizedFinite_uniform_C2_approx
~~~

and its load-bearing Fourier/Finsupp, zero-mode, twice-primitive and lower-jet helpers print only

~~~text
[propext, Classical.choice, Quot.sound]
~~~

with no `sorryAx`.

## What became formally true

**PROVED.**

For every positive aperture (L), every complex-valued (C^2) function (h) with

[
operatorname{tsupport}(h)subset (0,L),
]

and every (arepsilon>0), there exist (Nge 1) and centered finite coefficients (u) such that, with

[
q(x)=	exttt{localizedFiniteFunction }L,N,u,x,
]

Lean proves

[
q(0)=0
]

and uniformly for (xin[0,L]),

[
lVert q(x)-h(x)Vert<arepsilon,
]

[
lVert q'(x)-h'(x)Vert<arepsilon,
]

[
lVert q''(x)-h''(x)Vert<arepsilon.
]

Here (q') and (q'') are represented by the repository's exact formula-level first and second jets.

The proof uses the pinned Mathlib AddCircle Fourier span, removes the zero Fourier mode before frequency division, integrates the nonzero modes twice, reconstructs the exact centered `Fin (2*N+1)` basis, and anchors only the zero mode to force (q(0)=0).

The theorem is deliberately formula-level. It does **not** claim that the raw hard-window zero extension of (q) is globally (C^2).

## What changed

Before #91, F0-B1C still contained two substantial uncertainties:

1. whether the exact pinned AddCircle finite Fourier span could be transported into the repository's normalized centered coordinates; and
2. whether approximation could be made strong enough simultaneously for WCONT and the #88 endpoint projection.

Both are now settled.

The proved topology is stronger than the minimal WCONT target:

~~~text
uniform q -> h
uniform q' -> h'
uniform q'' -> h''
~~~

on one fixed aperture.

Therefore:

- fixed-(L) (L^1) convergence of (q-h) follows;
- fixed-(L) (L^1) convergence of the second-jet error follows;
- endpoint first- and second-jet errors tend to zero automatically;
- the value endpoint is anchored exactly, not merely approximately.

Generic Stone-Weierstrass packaging and a Fejer-first construction are no longer needed on the primary route.

## Upstream implications

### Exact zero moment reduction

**DERIVED — not yet separately formalized.**

PR #88 proves

[
q(0)=rac{1}{sqrt L}M_0(u).
]

For (L>0), #91 gives (q(0)=0) exactly, hence

[
M_0(u)=0.
]

Thus the #88 correction coefficients simplify from

[
c_{-1}=rac{M_1-M_2}{2},qquad
c_0=M_2-M_0,qquad
c_1=-rac{M_1+M_2}{2}
]

to

[
c_{-1}=rac{M_1-M_2}{2},qquad
c_0=M_2,qquad
c_1=-rac{M_1+M_2}{2}.
]

The correction coefficient sum is then exactly zero, so the projection does not disturb the already-anchored endpoint value.

The next projection theorem therefore needs quantitative control only of (M_1) and (M_2).

### Endpoint moments from endpoint jets

Let

[
b_L=i,rac{2pi}{L}.
]

PR #88 gives

[
q'(0)=b_L,L^{-1/2}M_1,
qquad
q''(0)=b_L^2,L^{-1/2}M_2.
]

Hence, for (L>0),

[
|M_1|
=rac{L^{3/2}}{2pi}|q'(0)|,
]

[
|M_2|
=rac{L^{5/2}}{4pi^2}|q''(0)|.
]

These are **DERIVED** exact norm consequences of already proved identities.

## Downstream implications

Let (c) denote the formula-level three-mode correction and (p=q+c) the projected interior finite Fourier formula.

Because only modes (-1,0,+1) occur, the following fixed-(L), (N)-independent bounds are **DERIVED / next formalization target**.

### Function correction

Using (|	exttt{localizedMode}_{L,n}(x)|=L^{-1/2}),

[
int_0^L |c(x)|,dx
le
rac{L^2}{2pi}|q'(0)|
+
rac{L^3}{2pi^2}|q''(0)|.
]

### Second-jet correction

The zero mode contributes no second derivative and the (pm1) modes have frequency magnitude (2pi/L). Therefore

[
int_0^L |c''(x)|,dx
le
2pi |q'(0)| + L|q''(0)|.
]

### Consequence for #91 epsilon-approximants

For the strict-collar target, (h'(0)=h''(0)=0). If #91 is invoked with uniform error (<arepsilon), then

[
|q'(0)|<arepsilon,qquad |q''(0)|<arepsilon.
]

Thus, still **DERIVED**,

[
int_0^L |p-h|
le
left(
L+rac{L^2}{2pi}+rac{L^3}{2pi^2}
ight)arepsilon,
]

and at the formula-level second jet,

[
int_0^L |p''-h''|
le
(2L+2pi)arepsilon.
]

This means F0-B1C-B should not require a new approximation theory. It should be a finite-dimensional estimate plus the legal hard-window derivative identification.

## Resurrected routes

No previously killed route becomes preferable to the primary path.

- Generic Stone-Weierstrass infrastructure is **SUPERSEDED** for this obligation.
- Direct Fejer is **DORMANT FALLBACK**.
- Boundary-killer multiplication remains a **READY FALLBACK**, but its quotient/product burden is now clearly larger than the exact #88 projector.
- F0-B2 direct localized-additive continuity remains a fallback only; WCONT-A + #91 is shorter.
- The source-faithful lane remains parallel and is unchanged by #91.

## New RH-relevant clues

### Constrained finite negative witness

**LEAD / HYPOTHESIS.**

If F1 is reached through the projected #91 approximants, the finite negative vector automatically lies in the three-moment sector

[
mathbf1^Tu=0,qquad
mathbf1^TDu=0,qquad
mathbf1^TD^2u=0.
]

The canonical matrix already satisfies the exact displacement identity

[
DM-MD=gmathbf1^T-mathbf1 g^T.
]

A future F1 witness therefore lives in a sector that annihilates the same low Krylov moments appearing in the rank-two displacement law. This may simplify commutator/Krylov identities after F1.

This is not yet a theorem beyond the individual proved ingredients.

## Falsification checks

The primary approximation risk has moved.

No longer live:

- exact AddCircle density availability;
- extraction to finite integer coefficients;
- centered coordinate representation;
- zero-mode removal before frequency division;
- reconstruction of the second jet;
- fixed-(L) lower-jet control.

Still live:

1. formalizing the (M_0=0) specialization cleanly without hidden division assumptions;
2. proving the explicit correction (L^1) bounds with the repository's normalized modes;
3. identifying the global second derivative of the **complete projected hard-window vector** with the interior second jet almost everywhere / strongly enough for the WCONT integral;
4. preserving one fixed support envelope;
5. transferring the strict negative W1 margin with an explicit error choice;
6. avoiding any use of the correction alone as an admissible hard-window (C^2) test.

Fastest falsifier: attempt the explicit three-mode correction estimates directly. There is no reason to build additional Fourier infrastructure first.

## Highest-leverage next moves

### F0-B1C-B — NOW

The next PR should theorem-lock:

1. (q(0)=0Rightarrow M_0=0) for (L>0);
2. exact/safe norm bounds converting (q'(0),q''(0)) into (M_1,M_2);
3. fixed-(L), (N)-independent (L^1) bounds for the three-mode correction and its second jet;
4. legality of the complete projected hard-window vector via F0-B1A;
5. the production existential theorem:
   for every strict-collar (C^2) target and every (eta>0), there exist (Nge1,u) with `BoundaryFlatCoefficients N u` such that the legal hard-window vector (p) satisfies
   [
   int |p-h|<eta,
   qquad
   int |p''-h''|<eta.
   ]

### Then — strict sign transfer

Compose F0-B1C-B with W1 and WCONT-A, choose the approximation error below the strict negative margin, and obtain one legal finite (p) with

[
operatorname{Re}W(p,p)<0.
]

### Then — F1

Cash out through F0-B1A:

[
operatorname{Re}
operatorname{quadraticForm}
(	exttt{canonicalSourceMatrix }L,N)u<0.
]

Preferred F1 retains `BoundaryFlatCoefficients N u`.

## Standing questions

**What becomes possible that was not possible before?**  
The raw infinite-to-finite approximation problem is closed. The internal route now reduces to finite-dimensional projection stability plus strict sign transfer.

**Where does the RH-relevant clue propagate?**  
Through the exact moment constraints into the canonical finite negative sector and, after F1, potentially into the displacement/Krylov structure.

**What test most efficiently tells us whether the clue is real?**  
Formalize the explicit correction bounds above. If they close with constants depending only on fixed (L), F0-B1C-B should follow immediately.

**RH remains OPEN.**

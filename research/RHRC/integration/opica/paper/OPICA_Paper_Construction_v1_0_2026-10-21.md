---
title: "OPICA: a source-typed obstruction-preservation architecture"
subtitle: "Paper construction, adversarial audit, and Lean implementation contract"
author: "Zeta23 research synthesis for Marcus Hermansson"
date: "21 October 2026 | Step 1: paper only | RH and Step 4 OPEN"
lang: en
fontsize: 10pt
papersize: a4
geometry: "margin=23mm, headheight=15pt"
colorlinks: true
linkcolor: blue
urlcolor: blue
toc: true
toc-depth: 2
header-includes:
  - \usepackage{amsmath,amssymb,mathtools,booktabs,longtable,microtype}
  - \usepackage{xurl}
  - \usepackage{fancyhdr}
  - \pagestyle{fancy}
  - \fancyhf{}
  - \fancyhead[L]{\small ZETA23 / OPICA PAPER CONSTRUCTION}
  - \fancyhead[R]{\small RH OPEN}
  - \fancyfoot[C]{\thepage}
  - \allowdisplaybreaks
  - \setlength{\emergencystretch}{3em}
---

# Abstract and exact deliverable

**OPICA** means **Obstruction-Preservation and Independent-Constraint Architecture**. This paper constructs its mathematical core, rather than merely naming a proposed universal barrier. It proves local pole/jet transport, correction-aware finite composition, stability of observed exponential rates under controlled perturbations, an analytic pole-to-range obstruction, and precise tests for loss of observability and purported overdetermination. These statements are deliberately typed by their mathematical spaces and hypotheses. A local residue, an input Taylor coefficient, and a global energy exponent are not automatically the same invariant.

The source audit rejects several assertions in the submitted notes. In particular, M0608's compact observation kernel is not the zeta-containing completion; an integrated Gram kernel need not have rank one; a bound on a chosen quadratic observation is not an eigenvalue bound; and seven evaluations of a six-parameter identity need not be inconsistent. The paper includes the exact corrections, not silently repaired versions of the proposals.

**The main construction:** regard an obstruction as a class modulo a precisely declared negligible/background space. Prove that a specified transformation induces an injective map on that class, or an explicitly controlled equivalence of observed rates. Entire or boundary terms must either belong to the declared background space or be retained in a correction ledger. Composition is then a theorem. Passage to an infinite construction requires a separate topology or accumulated-error theorem.

**Authority:** every new theorem proved below is **DERIVED / PAPER**, with a self-audit and finite exact controls. No new Lean theorem, compiler run, GitHub change, independent referee review, or improved zeta zero-free region is claimed. Native applications identify their already-formal inputs separately from inherited paper inputs. J5.2, DC1/DC2 and MS1 do not acquire Lean authority through citation here.

**Outcome:** the restricted architecture is constructed on paper. The claim that all future RH proofs must leave this architecture, or must be nonlinear, is rejected. An independent inequality on an existing linear representation could still close Step 4. This paper neither proves that inequality nor declares it impossible. Repository construction is reserved for the user's next message.

# 1. Evidence on the table

## 1.1 Scope and precedence

This is an audit of the proposed OPICA architecture and its relevant dependencies, not a fresh proof of every sentence in the project. The basis is the supplied proposal chain, the latest session handover, live repository references and selected source blobs, live Drive reads, and original mathematical source blocks in the 16,159-page handover.

The live repository main reference is

`97926d6a949fed7af0429a373b47abc772012834`,

with tree

`3b8fb2b29f53247ad5143a603c047e160bddd37c`.

PR #292's recorded head is `87e7221afb80fa45fa5f437dc6ac368f5affbb5b`. Live metadata says that the PR is merged, although its prose body still contains earlier statements that it is open and unmerged. Metadata takes precedence for that operational fact. The stale body is not used to infer current release approval or mathematical truth. [R1]

The locally available repository ZIP supplied 2,330 file bodies, including 1,026 Lean sources and 35 workflows. Their local Git-blob and SHA-256 inventory was regenerated. Three relevant source blobs were independently fetched from the pinned live commit and compared with this inventory. This turn does **not** repeat the earlier all-file live-tree comparison or the full compiler audit. The pin is Lean 4.33.0-rc2 with Mathlib commit `51e6992efd06126df61a496bebf8f49482a4e129`.

The fresh check-runs response reports 55 checks at the PR head. Its full compressed payload exceeded the displayed response budget. The earlier detailed harvest of 53 successes and two skips, classified into 15 formal, 10 regression and 30 research-producing checks, remains **inherited evidence**, not a newly recounted or replayed harvest. No workflow was started here. [S1]

The Drive root, the complete session learned-state Markdown and the current DC/MS Google Doc export were read through the live connector. The MD's 100,942-byte content has SHA-256 `be9a308208d4a11f5c6673dae214fe9cbe126389517cd23809edfc850ba45b9e`, matching the previous delivery record. The DC/MS text export is 27,129 bytes, SHA-256 `d8a556786f9039430b5a790b8987ae600e0b32d9e9ad6de61b3e27e95026677b`. This is source identity, not proof validation.

Original M0608 pages 8535–8539 were read directly from the large handover, and the decisive page 8536 was also rendered and visually checked. Its source body and selected M0500, M0659, M1152, C05 and Path D originals were recovered from the existing joint evidence packet. The earlier full-capsule verification of 8,037 files is historical; it was not repeated here. Neither the new root listing nor this targeted reading is represented as a fresh recursive audit of every Drive folder. [S1–S8]

The project README and Toolkit Ledger explicitly prohibit promotion of architecture, analogy, finite checks or a dashboard into mathematical proof. Their early operational details are historical; their distinction between exact mathematical proof and research governance remains applicable. [S9]

## 1.2 Native mathematical inventory

| Item | Available evidence | What it does not supply |
|---|---|---|
| Literal source and native transforms | Pinned Lean source and physical-transform adapters | A bound on every positively damped prime field |
| Actual zero multiplicity and input jet | `NativeZeroJetAnalyticFactors`, `NativeActualInputZeroJets`, and related modules | A contradiction merely because a holomorphic input has a nonzero derivative |
| Same-state Step 1–3 output | The original detector, finite image, selected state and physical fields are explicitly connected | Equality of all those vectors or a supplied Step 4 upper |
| Step 4 sufficiency cuts | Conditional A-X, B-Y and original C-Schur implications | Any of their open antecedents |
| Contact-to-polarized-exterior transport | Original M0608, PAPER | Identity of its compact probe with the completion |
| Native logarithmic-window rate | M0659/M1196 J5.2, PAPER | A quiet window or a general rate theorem for every meromorphic field |
| Slow-moving source return | DC/MS continuation MS1, PAPER, self-reviewed | Arbitrary diagonal substitutions of changing parameters |
| Divisor-controlled low-mask comparison | DC1/DC2, PAPER, rederived in Section 7 | Exact preservation of an operator eigenvalue |
| Sharp signed heat-gap separator | Structural-pivot note, PAPER, proved again below | A native contact-to-defect construction |
| Initial local Lean kernel falsifiers | Historical receipts for 11 roots | New formal validation of the latest barrier proposals |

The old D2/WP4 continuum obligation, the 49 original requirements, and WP0–WP7 remain separately tracked. OPICA neither completes nor deletes them. A mathematical proof through a logically independent terminal cut would not make an unfinished D2 run retrospectively successful. [S1, S2]

## 1.3 Terminology and status

**PROVED (Lean/CI)** is reserved for an exact declaration on its checked source with its actual dependencies. **DERIVED / PAPER** means a written argument under explicitly identified inputs, without new compiler authority. **FINITE CHECK** means only the finite executed assertion. **LEAD** means an unproved research possibility. **OPEN** means not established.

The phrase *independent constraint* below has two meanings that must not be confused. A separation condition such as a vector lying outside a range is a precise mathematical assertion. Whether its proposed proof uses genuinely new arithmetic information, rather than assuming the sought conclusion under another name, is a provenance and dependency audit. This paper does not claim a decision procedure for logical independence, novelty or all possible proofs.

# 2. Source and notation firewall

## 2.1 The literal original system

Use the established source normalization

$$
 s_0=1/4096,
 \qquad q=*_{n\ge1}\frac{\mathbf1_{[-c_n,c_n]}}{2c_n},
 \qquad c_n=\frac{s_0}{n(n+1)},
 \qquad P=\partial_t^2-\tfrac14.
$$

Then

$$
 k=Pq,\qquad j=P^2q,\qquad h=k*k=q*j.
$$

The positive density is $q$; the derivative sources are signed. With negative-exponent Laplace convention,

$$
 Q_0(z)=\int e^{-zt}q(t)\,dt,
 \qquad J(z)=(z^2-\tfrac14)^2Q_0(z).
$$

Keep the actual locally finite measures

$$
 N=\sum_{n\ge1}n^{-1/2}\delta_{\log n},\quad
 M_\mu=\sum_{n\ge1}\mu(n)n^{-1/2}\delta_{\log n},\quad
 \Pi=\sum_{n\ge2}\Lambda(n)n^{-1/2}\delta_{\log n}.
$$

Their native identities and fields are

$$
 M_\mu*N=\delta_0,\quad N*\Pi=tN,
 \quad U_j=(tN)*j,\quad X_j=\Pi*j=M_\mu*U_j.
$$

All prime powers are retained. The current completion is

$$
 c(t)=(-e^{-t/2}+2e^{-3t/2})\mathbf1_{t\ge0},\qquad
 \mathfrak a=c*N,\qquad Y_j=c*U_j,\qquad
 \mathfrak a*X_j=Y_j.
$$

Its rational factor is

$$
 r_c(z)=\frac{z-1/2}{(z+1/2)(z+3/2)}.
$$

The initial safe transform identities are

$$
 \widehat X_j(z)=-J(z)\frac{\zeta'(z+1/2)}{\zeta(z+1/2)},
 \qquad \widehat Y_j(z)=-r_c(z)J(z)\zeta'(z+1/2).
$$

The formulas are subsequently transported only across domains where the actual integrals or their legitimate meromorphic continuations have been identified. No pointwise cancellation at a totalized division-by-zero value is licensed. [R2–R5]

## 2.2 Four unrelated order parameters

Throughout this paper:

- $m\ge1$ is the multiplicity of a hypothetical zeta zero;
- $q_{\rm neu}$ is an elementary-neutrality order at contact;
- $r$ is an inverse-factor count;
- $k$ is the vanishing order of an abstract holomorphic multiplier.

The source derivative order is denoted $d_{\rm src}$ when it could be confused with $m$. The centered zero is $\lambda=\rho-1/2$; its displacement is $\delta=\Re\lambda>0$. The spatial aperture is $\ell$, the compact probe radius is $b$, and the causal kernel is $\mathfrak a$. This notation prevents several substitutions made in the incoming notes.

## 2.3 Two distinct kernels in the contact route

The original M0608 construction starts from a constrained contact source $f$ for which

$$
 w=W*f=N_{q_{\rm neu}}\quad\text{on }(-\ell,\ell),
$$

where

$$
 N_{q_{\rm neu}}(x)
 =\sum_{\sigma=\pm1}\sum_{j=0}^{q_{\rm neu}-1}
       \alpha_{\sigma j}x^je^{\sigma x/2}.
$$

It is generally not the zero function. Choose the specified compact Gevrey probe $\psi$, with $0<b<\ell$, and form the explicitly changed polarized source $h_f=\psi*\widetilde f$. The normal family is annihilated only in the appropriate interior convolution. M0608 then defines

$$
 \kappa_{\rm obs}(u)=\psi(b-u)\mathbf1_{[0,2b]}(u),
 \qquad v(t)=w(\ell+t)\mathbf1_{t\ge0},
$$

$$
 Q_{\rm obs}(t)=(W*h_f)(\ell-b+t),\qquad t\ge0.
$$

The actual identity is

$$
 \boxed{Q_{\rm obs}=\kappa_{\rm obs}*v+H_N,}
 \tag{2.1}
$$

$$
 H_N(t)=\mathbf1_{[0,2b]}(t)
        \int_t^{2b}\kappa_{\rm obs}(u)
                       N_{q_{\rm neu}}(\ell+t-u)\,du.
$$

In particular,

$$
 \widehat\kappa_{\rm obs}(z)=e^{-bz}\widehat\psi(-z).
$$

This is a compact probe transform. It does **not** contain a factor $\zeta(z+1/2)$ by definition. In the visible off-line situation it is nonzero at $\lambda$. Both $v$ and $Q_{\rm obs}$ retain the specified nonzero exterior residue. By contrast, $\widehat{\mathfrak a}=r_c\zeta$ vanishes at the zero. [S3, §4.3–4.5]

The statement in the newest jet note that “$\kappa$ is already the causal completion” is false for (2.1). A different stable-input completion equation is legitimate, but its symbols cannot be identified with (2.1). This paper consistently labels those two edges separately.

The raw M0608 normal family has dimension $2q_{\rm neu}$ before parity restriction. The six-dimensional family in M1152 is obtained after a particular compact pole inverse. It is not a universal six-parameter description of every contact source. The later M0608 allowed-division argument also repairs the earlier question about simplicity of the constrained generator's real zeros. It retains all its source/domain hypotheses; PSD alone is not a substitute for that proof. [S3, §3; S4, §6]

# 3. Audit verdict: what is retained and what is rejected

This table addresses the substantive claims in the proposal sequence, including the assistant's earlier broad wording. The detailed audit inventory is supplied separately in machine-readable form.

| Claim in the proposed architecture | Disposition and repair |
|---|---|
| All native linear operators lie in $(\zeta)$ or $1+(\zeta)$ | False as a classification. Constants such as 2 and other analytic multipliers are outside both. Use exact local vanishing order; treat the two special classes as corollaries. |
| The ideal $(\zeta)$ is a useful proper ideal in any transform algebra | Specify holomorphic germs. In the field of meromorphic germs, a nonzero $\zeta$ is invertible and generates the whole field. |
| Eliminating a pole eliminates the obstruction | Not without the analytic representative and observation. Completion transfers it to a leading jet. |
| Any entire addition is harmless after completion | False. An analytic addition can cancel the completed leading jet. Retain the affine correction ledger or prove a stronger vanishing order. |
| M0608's $\kappa$ already vanishes at zeta zeros | False for its compact observation kernel; see (2.1). |
| Completing twice annihilates history at every later jet | False. At higher derivative order the history can contribute, and the Leibniz binomial coefficient matters. |
| Integral of rank-one kernels is rank one | False. A Gram integral can have arbitrarily large finite rank. |
| DC1 preserves the exact largest eigenvalue | Unsupported. It bounds a specific bilinear quantity on a stated coefficient class. |
| High-primitive means $a,b>B$ | False. It means $\max(a,b)>B$. |
| For balanced product coefficients, the common gcd is coprime to both primitives | False. That restriction comes from squarefree single-Möbius products, not general Dirichlet convolution coefficients. |
| Absorbing factors into a kernel preserves the old quadratic mask | Not automatically. It preserves the unmasked field; masked comparison needs a second estimate. |
| Removing the diagonal removes the coherent rational channel | False. That channel includes off-diagonal pairs. |
| A contrast annihilating the coherent channel still controls the native sum | Requires a recovery/observability theorem; generic contrast loses the target. |
| Seven spectral equations for six coefficients imply inconsistency | False without an independently nonzero compatibility residual. The equations may already be identities. |
| Any $L^1$ log-dilation weight defines the needed measure | False. The comb pairings can grow as $e^{t/2}$; stronger integrability or a fully specified regularization is required. |
| Evaluating an analytically continued transform proves a convergent moment | False. Analytic continuation cannot be substituted for an inadmissible integral. |
| A quadratic weight is automatically a new map outside the log-dilation family | False. The map is still linear in the weight $h=|\psi|^2$. |
| The spatial Fourier commutator produces a self-dual defect | The simplest commutator produces an anti-self-dual defect; Section 10 proves this. |
| All viable proofs must be nonlinear or couple different zeros | Not established, and not needed. An independent estimate on a linear map may suffice. |
| The four listed candidate routes are barrier-free by construction | Rejected. They are leads with unproved native interfaces and independent constraints. |

The corrected architecture is not a list of forbidden mathematical techniques. It tells us exactly what the proved transformations preserve, what they discard, and which extra condition is needed to turn a preserved obstruction into a contradiction.

# 4. Local analytic layer: poles, ideals and transferred jets

## 4.1 Germs, representatives and observable coefficients

Fix $\lambda\in\mathbb C$ and set $x=z-\lambda$. Let $\mathcal O_\lambda$ be the ring of holomorphic germs at $\lambda$ and let $\mathcal M_\lambda$ be its fraction field, the meromorphic germs. Equality of meromorphic germs is equality on a sufficiently small punctured neighborhood. It does not constrain an arbitrary assigned point value at $\lambda$.

A nonzero meromorphic germ has a unique finite order $n\in\mathbb Z$ and expression

$$f=x^n u,\qquad u\in\mathcal O_\lambda,\quad u(\lambda)\ne0.$$

The leading coefficient in this fixed coordinate is $u(\lambda)$. A **visible simple-pole datum** is

$$
 f=R/x+h,\qquad h\in\mathcal O_\lambda,\quad R\ne0.
 \tag{4.1}
$$

The simple-pole space modulo analytic backgrounds is

$$
 \mathcal P_\lambda=x^{-1}\mathcal O_\lambda/\mathcal O_\lambda.
$$

The residue map identifies it with $\mathbb C$. This assertion uses the fixed local coordinate. A general coordinate change must carry its Jacobian; the native shift $s=z+1/2$ has derivative one.

For $k\ge1$, define the completed leading-jet quotient

$$
 \mathcal J_{k,\lambda}
 =x^{k-1}\mathcal O_\lambda/x^k\mathcal O_\lambda.
$$

Its scalar coordinate is $g^{(k-1)}(\lambda)/(k-1)!$. We use *Taylor coefficient* for this normalized quantity and *jet derivative* for $g^{(k-1)}(\lambda)$. Confusing the two causes factorial errors.

## 4.2 Theorem L1: general local multiplier law

**Statement.** Suppose (4.1) holds and $M=x^ku$ is a nonzero holomorphic germ of finite order $k\ge0$. Then

$$
 Mf=x^{k-1}u(R+xh).
 \tag{4.2}
$$

Its exact meromorphic order is $k-1$, and its leading coefficient is $u(\lambda)R\ne0$.

For $k=0$, it has a simple pole with residue $u(\lambda)R$. For $k\ge1$, its analytic extension has all derivatives below $k-1$ zero and

$$
 \boxed{(Mf)^{(k-1)}(\lambda)
 =(k-1)!\,u(\lambda)R\ne0.}
 \tag{4.3}
$$

**Proof.** Multiply the representatives on the punctured neighborhood to obtain (4.2). The factor $u(R+xh)$ is holomorphic and nonzero at $\lambda$, because its value is $u(\lambda)R$. The asserted order follows. For $k\ge1$, the right-hand side supplies the analytic extension; its first nonzero Taylor coefficient occurs at degree $k-1$, and differentiation gives (4.3). This proves both existence and uniqueness of the relevant extension. $\square$

This theorem classifies finite nonzero holomorphic multipliers by order. It does not say that every operator under discussion is such a multiplier, or that its transform identity is valid in the native functional domain.

## 4.3 Theorem L2: the local zero ideal and two important subclasses

Let $Z\in\mathcal O_\lambda$ have zero order $m\ge1$:

$$Z=x^m v,\qquad v(\lambda)\ne0.$$

Then $(Z)=(x^m)$ and the truncated Taylor map gives

$$
 \boxed{\mathcal O_\lambda/(Z)
 \simeq\mathbb C[X]/(X^m).}
 \tag{4.4}
$$

**Proof.** The germ $v$ is a unit, so multiplication by it does not change the generated ideal. Taylor's formula writes each germ uniquely modulo $x^m$ as its polynomial of degree less than $m$. The truncated Taylor map is a surjective ring homomorphism with kernel $x^m\mathcal O_\lambda$, proving (4.4). $\square$

**Residual law.** For $M=1+Zb$, $b\in\mathcal O_\lambda$,

$$
 \operatorname{Res}_\lambda(Mf)=R,
 \qquad Mf-f\in x^{m-1}\mathcal O_\lambda.
 \tag{4.5}
$$

Indeed $Zbf=x^{m-1}vb(R+xh)$, while $M(\lambda)=1$. This remains true for every finite product of multipliers congruent to one modulo $(Z)$, including every nonnegative integer power of $1-Zb$; the class $1+(Z)$ is multiplicatively closed.

**Completion law.** For $M=Za$ with $a(\lambda)\ne0$,

$$
 (Mf)^{(m-1)}(\lambda)
 =(m-1)!\,v(\lambda)a(\lambda)R.
 \tag{4.6}
$$

Multiplication by $M$ induces a well-defined isomorphism

$$
 \mathcal P_\lambda\longrightarrow\mathcal J_{m,\lambda}.
 \tag{4.7}
$$

To check well-definedness, an analytic change to $f$ is multiplied into $x^m\mathcal O_\lambda$. The map on the one-dimensional coordinates is multiplication by the nonzero scalar $v(\lambda)a(\lambda)$, hence is bijective.

For the native centered zeta germ, $Z(z)=\zeta(z+1/2)$ and

$$v(\lambda)=\frac{\zeta^{(m)}(\rho)}{m!}.$$

For the literal $\widehat X_j$, $R=-mJ(\lambda)$, so its completed derivative is exactly

$$
 \boxed{\widehat Y_j^{(m-1)}(\lambda)
 =-r_c(\lambda)J(\lambda)\zeta^{(m)}(\rho).}
 \tag{4.8}
$$

This is nonzero in the visible case, and is consistent with a holomorphic, rapidly decaying completed input. It is not an independent contradiction. Actual integral/jet identification is supplied by the pinned native modules, not by the quotient notation alone. [R2–R5]

## 4.4 Theorem L3: repeated completions and exact normalization

For $p\ge1$ and $M=Za$ as above,

$$
 \operatorname{ord}_\lambda(M^pf)=pm-1,
$$

$$
 (M^pf)^{(pm-1)}(\lambda)
 =(pm-1)!\,[a(\lambda)v(\lambda)]^pR.
 \tag{4.9}
$$

This is L1 applied to $M^p=x^{pm}(av)^p$.

In a genuinely already-completed equation $Q-H=Mf$, applying another completion $A$ of order $m$ gives

$$
 \boxed{
 [A(Q-H)]^{(2m-1)}(\lambda)
 =\binom{2m-1}{m}A^{(m)}(\lambda)
                    (Q-H)^{(m-1)}(\lambda).
 }
 \tag{4.10}
$$

Only that term survives the Leibniz sum. The binomial coefficient is essential. At order $m-1$, both sides are zero. At order $2m-1$, **$AH$ need not vanish** unless it is explicitly subtracted or given additional zero order. The assertions “compact history is entire” and “all its completed higher jets vanish” are different statements.

## 4.5 Theorem L4: affine composition with a correction ledger

Let $f_0$ satisfy (4.1), and for $i=0,\ldots,n-1$ let

$$f_{i+1}=M_i f_i+B_i,$$

where the $M_i$ are nonzero holomorphic germs, of orders $k_i\ge0$, and the $B_i$ are holomorphic germs. Define

$$
 C_0=0,\qquad C_{i+1}=M_iC_i+B_i,
 \qquad P_n=\prod_{i=0}^{n-1}M_i.
$$

Then

$$
 \boxed{f_n-C_n=P_nf_0,}
 \tag{4.11}
$$

and, putting $K_n=\sum_{i<n}k_i$,

$$
 \operatorname{ord}_\lambda(f_n-C_n)=K_n-1,
 \qquad
 \operatorname{lead}_\lambda(f_n-C_n)
 =R\prod_{i<n}\operatorname{lead}_\lambda(M_i)\ne0.
 \tag{4.12}
$$

**Proof.** The assertion holds at $n=0$. If it holds at $i$, then

$$
 f_{i+1}-C_{i+1}
 =M_i(f_i-C_i)=M_iP_if_0.
$$

Induction proves (4.11). Factoring every multiplier into its monomial and holomorphic unit proves (4.12) exactly as in L1. Explicitly,

$$C_n=\sum_{j<n}\left(\prod_{j<i<n}M_i\right)B_j.$$

$\square$

The invariant is attached to the **corrected expression**. Without that qualification, $f_0=1/x$, $M_0=x$, $B_0=-1$ gives $f_1=0$. An arbitrary analytic background is negligible for a raw pole, but not for the value of its completed analytic image.

The raw $f_n$ has the same leading class as $f_n-C_n$ if $C_n\in x^{K_n}\mathcal O_\lambda$. This stronger condition must be proved, not inferred from analyticity alone.

## 4.6 Native contact application, with the corrected kernel types

In (2.1), let $R_v=\operatorname{Res}_\lambda\widehat v\ne0$. Since $\widehat\kappa_{\rm obs}(\lambda)\ne0$ and $\widehat H_N$ is entire, L1 gives

$$
 \operatorname{Res}_\lambda\widehat Q_{\rm obs}
 =\widehat\kappa_{\rm obs}(\lambda)R_v.
$$

Apply the *separate* completion $A(z)=r_c(z)Z(z)$. Because $A\widehat H_N$ has zero order at least $m$,

$$
 \boxed{
 [A\widehat Q_{\rm obs}]^{(m-1)}(\lambda)
 =\frac{r_c(\lambda)\zeta^{(m)}(\rho)}{m}
    \widehat\kappa_{\rm obs}(\lambda)R_v\ne0.
 }
 \tag{4.13}
$$

Using M0608's actual $R_v=m e^{\ell\lambda}F_f(-i\lambda)$ cancels the displayed $1/m$. This is the correct history-independent jet for the compact-probe equation. It is a contact-source observation, not automatically $\widehat Y_j$ of the fixed original $j$.

If instead a separately defined equation already contains a zeta completion, use L3, not (4.13). Both algebraic calculations are valid in their appropriate types. Neither forces a holomorphic completed input's first nonzero derivative to be zero.

## 4.7 Theorem L5: local preservation does not pass through every limit

Finite composition does not authorize a limit in an unrelated topology. For example, let $\Re\lambda=\delta>0$ and

$$
 f_n(t)=e^{\lambda t}\mathbf1_{t\ge n}.
$$

On every fixed compact time interval, $f_n$ is eventually zero. On $\Re z>\delta$,

$$
 \widehat f_n(z)=\frac{e^{-n(z-\lambda)}}{z-\lambda}
$$

converges locally uniformly to zero. But each meromorphic continuation has residue one at $\lambda$. The convergence does not extend uniformly to a small circle surrounding $\lambda$.

A legitimate sufficient topology is the following: if $g_n$ and $g$ are meromorphic on a common disk with no pole other than the center and $g_n\to g$ uniformly on its radius-$r$ boundary circle, then

$$
 |\operatorname{Res}_\lambda(g_n-g)|
 \le r\sup_{|z-\lambda|=r}|g_n(z)-g(z)|\to0.
 \tag{4.14}
$$

This is the residue integral and its length estimate. It identifies a concrete condition required for an infinite preservation claim. The causal example is not a second native zeta system; it defeats only the unrestricted limit inference.

# 5. Energy layer: observed rates rather than operator eigenvalues

## 5.1 Schedules and negligible observations

Let $T_n>0$ and $T_n\to\infty$. Monotonicity is not needed. For a real or complex sequence $u$, define the magnitude rate sequence

$$\gamma_T(u)_n=\frac{\log(1+|u_n|)}{2T_n}.$$

For real $u$, define

$$\gamma_T^+(u)_n=\frac{\log(1+\max(u_n,0))}{2T_n}.$$

A sequence is **subexponential on the schedule**, written $u\in\mathcal S_T$, if $\gamma_T(u)_n\to0$. This includes constants, polynomials in $T_n$, and $e^{\sqrt{T_n}}$, but not $e^{cT_n}$ for $c>0$. This definition concerns the actual unnormalized observation, not an angle or a normalized correlation.

The set $\mathcal S_T$ is a vector space over constant real or complex scalars and is closed under finite products. Indeed, $1+|u+v|\le(1+|u|)(1+|v|)$ and $1+|uv|\le(1+|u|)(1+|v|)$; divide their logarithms by $2T_n$. Constant scalar multiplication adds only a bounded logarithmic cost. It is **not** an ideal in the ring of all sequences: it contains 1, so such an ideal would be the whole ring. We will use it only as an additive background space or as a multiplier algebra with explicitly controlled inverses.

## 5.2 Theorem E1: the elementary logarithmic comparison

For real $a,b$,

$$
 \boxed{
 |\log(1+\max(a,0))-\log(1+\max(b,0))|
 \le\log(1+|a-b|).
 }
 \tag{5.1}
$$

For real or complex $a,b$ the same bound holds with $|a|,|b|$ in place of their positive parts.

**Proof.** The positive-part map is 1-Lipschitz. Thus, with $d=|a-b|$,

$$
 1+\max(a,0)
 \le1+\max(b,0)+d
 \le(1+\max(b,0))(1+d).
$$

Taking logarithms gives one direction; interchanging $a,b$ gives the other. The magnitude version follows from the reverse triangle inequality. $\square$

## 5.3 Theorem E2: subexponential additive preservation

Suppose $u-v\in\mathcal S_T$. Then

$$\gamma_T(u)_n-\gamma_T(v)_n\to0.$$

For real sequences the corresponding positive-part difference also tends to zero. Consequently their existing limits agree, and their limsup and liminf rates agree even when the full limits do not exist.

**Proof.** Divide (5.1) by $2T_n$ and apply the squeeze theorem. The limsup/liminf claims follow by adding a sequence tending to zero. $\square$

In particular, if $E_n\ge0$, $E-Z\in\mathcal S_T$, and

$$\frac{\log(1+E_n)}{2T_n}\to\Theta,$$

then

$$
 \boxed{
 \gamma_T^+(Z)_n\to\Theta,
 \qquad\gamma_T(Z)_n\to\Theta.
 }
 \tag{5.2}
$$

For $\Theta>0$, $Z_n$ is eventually positive. To see this, choose $0<b<\Theta$; the full limit makes $E_n$ eventually larger than $e^{2bT_n}$, while the error is smaller than half that quantity. For $\Theta=0$, no eventual sign is asserted.

This is the correct abstract content of the masked-energy comparison. It does not refer to eigenvalues, ranks or a spectral norm of the kernel.

## 5.4 Theorem E3: tempered rescaling and its inverse cost

Let $a_n\ne0$ and assume

$$
 \frac{\log\max(|a_n|,|a_n|^{-1})}{2T_n}\to0.
 \tag{5.3}
$$

Then $\gamma_T(au)-\gamma_T(u)\to0$ for every sequence $u$. If $a_n>0$ and $u$ is real, the same holds for the positive-part rates.

**Proof.** With $C_n=\max(|a_n|,|a_n|^{-1})\ge1$,

$$C_n^{-1}(1+|u_n|)\le1+|a_nu_n|\le C_n(1+|u_n|).$$

Taking logarithms proves the result. For positive $a_n$, use $\max(a_nu_n,0)=a_n\max(u_n,0)$. $\square$

Nonzero finite multipliers alone do not suffice: $a_n=e^{-T_n}$ shifts a positive exponential magnitude rate. An upper bound on $a_n$ without a matching inverse bound also does not suffice. In particular, being a local analytic unit at each stage is not a uniform energy-budget theorem for changing translations or sources. Negative multipliers preserve magnitude rates but may reverse the positive-part observation; $u_n=e^{T_n}$ and $a_n=-1$ are a direct counterexample.

## 5.5 Theorem E4: finite and growing chains

For a fixed finite chain

$$z_{i+1,n}=a_{i,n}z_{i,n}+b_{i,n},$$

where each $a_i$ satisfies (5.3) and each $b_i\in\mathcal S_T$, magnitude rates are preserved from the first to the last sequence. Positive-part rates are preserved if all the $a_i$ are positive and all data real. This follows by alternating E2 and E3 a finite number of times.

For a number of stages $k_n$ that grows with $n$, the correct sufficient condition is on the **whole chain**. Define

$$
 A_n=\prod_{i<k_n}a_{i,n},
 \qquad
 B_n=\sum_{j<k_n} b_{j,n}\prod_{j<i<k_n}a_{i,n}.
$$

If $A$ satisfies (5.3) and $B\in\mathcal S_T$, then

$$z_{k_n,n}=A_nz_{0,n}+B_n$$

has the same magnitude rate as $z_{0,n}$; with $A_n>0$, also the same positive-part rate. The exact finite expansion proves the formula for each $n$, then E2–E3 apply. Individual fixed-stage estimates without these accumulated hypotheses are not enough.

For inequalities $Z_{n+1}\le A_n Z_n+D_n$, $A_n,D_n\ge0$, the corresponding propagated budget is

$$
 Z_N\le Z_0\prod_{i<N}A_i
       +\sum_{j<N}D_j\prod_{j<i<N}A_i.
 \tag{5.4}
$$

It follows by induction. Dropping the suffix products loses the amplification of each additive error. The example $A_i=2$, $D_i=0$, $T_N=N$ makes every individual factor's logarithmic cost negligible compared with $T_N$, while the total product has positive rate.

## 5.6 Theorem E5: quiet cofinal observations

If a nonnegative native observation has the full rate $\Theta\ge0$ and there is a cofinal sequence of the *same* observations satisfying

$$
 1+E(T_n)\le C_n e^{2b_nT_n},\quad C_n>0,
 \quad b_n\to0,
 \quad\frac{\log C_n}{2T_n}\to0,
$$

then $\Theta=0$. Take logarithms and use the full limit along this sequence. This is a conditional implication, not a window-production theorem.

For the Zeta23 original source, identifying that full rate with

$$\Theta=\sup_\rho(\Re\rho-\tfrac12)_+$$

is the additional source-correct J5.2 theorem at PAPER authority. It is not a consequence of E1–E5. The slow-moving-source version MS1 has its further hypothesis $d_{{\rm src},n}\log(d_{{\rm src},n}+2)=o(T_n)$ and its uniform source/completion estimates. [S5, S6]

# 6. The mathematical architecture and its composition theorem

## 6.1 Representation objects and faithful transfers

An **algebraic representation object** is a pair $(V,N)$ of a vector space and a designated background subspace. Linear maps between such objects use a common base field. The obstruction of $v\in V$ is its quotient class $[v]\in V/N$.

A linear transformation $T:V\to V'$ respects backgrounds when $T(N)\subset N'$. It then induces a map $\overline T:V/N\to V'/N'$. Call it **faithful for the declared obstruction** when that induced map is injective. The adjective applies to these spaces and this class, not to all information in the original source.

### Theorem C1: exact criterion and composition

A background-respecting $T$ is faithful if and only if

$$T^{-1}(N')=N.$$

Compositions of faithful background-respecting maps are faithful. Affine offsets are harmless in the quotient only if they lie in the target background; otherwise retain and subtract the correction ledger of L4.

**Proof.** The kernel of $\overline T$ consists exactly of classes represented by $v$ with $Tv\in N'$. Its triviality is the displayed equality, since $N\subset T^{-1}(N')$ already holds. The composition of injective induced maps is injective. An affine offset in $N'$ contributes zero class; the general offset statement follows from (4.11). $\square$

This criterion is not used to declare every native map faithful by definition. L1–L4 prove it for the explicitly identified local maps. E1–E4 prove the corresponding observational claims for the sequence layer. Every new source map still has to satisfy its own hypotheses.

## 6.2 Concrete instantiations

**Local pole carrier:** $(x^{-1}\mathcal O_\lambda,\mathcal O_\lambda)$. Analytic unit multipliers induce invertible scalar residue maps; residual multipliers in $1+(Z)$ induce the identity.

**Completed carrier:** $(x^{k-1}\mathcal O_\lambda,x^k\mathcal O_\lambda)$. A multiplier of exact order $k$ induces the isomorphism in L1–L2 from the pole carrier. The completion does not preserve membership in the old pole space as an observable; it transfers to a different declared carrier.

**Energy carrier:** real sequences modulo $\mathcal S_T$. E2 says that positive-part and magnitude rate sequences are well-defined up to a vanishing discrepancy on that quotient. Tempered invertible scales act faithfully by E3. Equality of exponential rates is coarser than equality modulo $\mathcal S_T$; two sequences can have equal rates without their difference being subexponential.

**Source identity:** the record must specify which physical field maps to each transform and which field is squared. The map $f\mapsto|f|^2$ is nonlinear and is not an automatic morphism between the above quotients. A pole-to-energy statement is a separate analytic theorem, not an abstract consequence of C1.

## 6.3 Theorem C2: a precise typed finite-path rule

For $i=0,\ldots,n$, let $S_i$ be a state space and $(\Omega_i,0_i)$ a pointed obstruction carrier. Let $o_i:S_i\to\Omega_i$ be the actual observation in that representation. For $i<n$, let $T_i:S_i\to S_{i+1}$ be an admissible source transition and $C_i:\Omega_i\to\Omega_{i+1}$ a zero-preserving carrier map such that

$$
 o_{i+1}(T_i s)=C_i(o_i(s))\quad\text{for every admitted state }s,
 \qquad C_i(w)=0_{i+1}\Longrightarrow w=0_i.
 \tag{6.1}
$$

Assume the transition also preserves the declared admissibility conditions, including source/domain identity. If $o_0(s_0)\ne0_0$ and $s_{i+1}=T_i s_i$, then $o_n(s_n)\ne0_n$.

**Proof.** If $o_i(s_i)\ne0_i$, zero-reflection in (6.1) gives $C_i(o_i(s_i))\ne0_{i+1}$. The commuting identity identifies this with $o_{i+1}(s_{i+1})$. Induction proves the claim. Carrier maps compose and remain zero-reflecting. $\square$

Full injectivity is sufficient but not necessary for this nonvanishing rule. C1 proves the stronger property for the local quotient maps. For an affine local transition, include its correction ledger in the state and observe the corrected quotient class. For energy, use the rate on the class of sequences for which that rate exists; E2–E4 prove the appropriate identity carrier map, with orientation retained.

An analytic bridge such as B1 can instead supply only the implication

$$
 o_i(s_i)\ne0_i\Longrightarrow o_{i+1}(T_i s_i)\ne0_{i+1}.
 \tag{6.2}
$$

The same induction uses this weaker edge. It does not invent an isomorphism between residues and energy exponents. For example, a nonzero pole excludes a weighted norm below its real part, whereas it does not by itself specify a full terminal-window limit.

For this project the admitted edge families are:

1. Local multiplier/affine edges from L1–L4, with their coordinate, exact multiplier order, nonzero unit and correction ledger recorded.
2. Observational additive/scaling edges from E2–E4, with the same horizon normalization, full accumulated cost and orientation recorded.
3. Source-identified analytic bridge implications such as B1/B2, or the separately cited native J5.2/MS1, with their actual hypotheses supplied.
4. Observation projections only when the target recovery condition of O1 and any required uniform recovery cost have been proved.

This theorem's induction is elementary. Its research content is not obtained by naming a desired edge admissible: the commuting identity or implication for each actual source must be proved using the preceding mathematical laws or a new independent theorem. No native upper, analytic bridge or contact condition is built into an opaque axiom. Finite composition does not license the changing-depth limit without L5 or E4's additional hypotheses.

## 6.4 What can actually yield a contradiction

Suppose a faithful path transports $[v]\ne0$ to $[Tv]\ne0$. If an **independently proved native theorem** also establishes $Tv\in N'$, then the two facts contradict one another. Similarly, a source-specific positive energy rate contradicts an independently established smaller rate, or a finite data vector outside a proved compatibility range contradicts its required membership.

C1 does not provide the membership theorem. Defining an acceptable object to be one lying in $N'$ does not establish that the genuine source is acceptable. Nor does “outside the two multiplier classes” prove the new operation is useful: it could simply destroy the target observation.

The generic preservation laws are consistent with nonzero obstruction data. For example $Z=x^m$, $f=1/x$, zero affine backgrounds, and $E(T)=e^{2\theta T}$ with $\theta>0$ satisfy the appropriate local and energy laws. This is an auxiliary model of the architecture, not a counterexample to native zeta. It shows why the generic laws alone contain no RH contradiction.

# 7. Native arithmetic application: exact masks and legal regrouping

## 7.1 The actual pair split

Fix a finite squarefree palette $Q$ on a whole window $I=[H,T]$, where $0\le H<T$. Let

$$
 D_Q=\sum_{d\mid Q}\mu(d)d^{-1/2}\delta_{\log d},
 \quad U_{d_{\rm src},Q}=D_Q*U_{d_{\rm src}},
 \quad b_Q=\prod_{p\mid Q}(1+p^{-1/2}).
$$

Then $\|U_{d_{\rm src},Q}\|_\infty\le b_Q\|U_{d_{\rm src}}\|_\infty$. Put

$$w_d(t)=d^{-1/2}U_{d_{\rm src},Q}(t-\log d).$$

For real coefficient sequences $x,y$, define

$$
 \mathcal L_B(x,y)=\int_I\sum_{d,e}
 \mathbf1_{\max(d,e)/\gcd(d,e)\le B(t)}
 x(d)y(e)w_d(t)w_e(t)\,dt,
$$

and let $\mathcal Q_B$ use the strict complementary inequality. The low mask includes the diagonal. The causal gap makes all sums finite on bounded time intervals. With $X_x=\sum_dx(d)w_d$,

$$
 \boxed{\mathcal Q_B(x,y)=\int_I X_xX_y-\mathcal L_B(x,y).}
 \tag{7.1}
$$

For complex coefficients, use the Hermitian expression and replace a doubled mixed term by twice its real part. The real formulas below apply to the actual real Möbius coefficients.

Writing $d=ha,e=hb$ with $(a,b)=1$ is a unique decomposition. It imposes no additional relation between $h$ and $ab$. For example, at $r=2,Y=10,Q=2$, the genuine balanced coefficient has

$$c_2(121)=1,\quad c_2(1331)=1.$$

The pair has $h=121,a=1,b=11$. Thus $(h,b)>1$ although $(a,b)=1$. A restriction $(h,abQ)=1$ would incorrectly discard this genuine term. Also $\max(a,b)>7$ does not imply both $a,b>7$. These are finite coefficient counterexamples, not asymptotic claims.

## 7.2 Lemma A1: divisor bounds with explicit order dependence

Let $d_\ell(n)$ count ordered factorizations of $n$ into $\ell\ge1$ positive integers. Then

$$
 d_\ell(ab)\le d_\ell(a)d_\ell(b),\qquad
 d_\ell(n)^2\le d_{\ell^2}(n),
 \tag{7.2}
$$

$$
 \sum_{n\le X}\frac{d_\ell(n)^2}{n}
 \le(1+\log X)^{\ell^2},
 \qquad
 \sum_{n\le X}\frac{d_\ell(n)}{\sqrt n}
 \le2\sqrt X(1+\log X)^{\ell-1},\quad X\ge1.
 \tag{7.3}
$$

**Proof.** At each prime, an ordered factorization is a weak composition of its exponent. Every composition of the exponent of $ab$ can be split into compositions of the exponents of $a$ and $b$, giving the first surjective counting bound. A pair of weak $\ell$-compositions of the same exponent is realized as the row and column sums of a nonnegative integer $\ell\times\ell$ array. A greedy row/column allocation constructs an array for every pair, giving the second inequality. Multiply the local inequalities over primes.

For the first sum in (7.3), replace $d_\ell^2$ by $d_{\ell^2}$ and expand its factorizations. Dropping the product restriction leaves the $\ell^2$-fold product of $\sum_{n\le X}1/n\le1+\log X$. For the second sum, sum the last factor first using $\sum_{v\le Y}v^{-1/2}\le2\sqrt Y$, then bound the remaining $\ell-1$ harmonic factors. $\square$

## 7.3 Theorem A2: low-mask control and the two mixed terms

Suppose $1\le B(t)\le B_*$, $V=\|U_{d_{\rm src},Q}\|_\infty$, and

$$|x(d)|\le A_xd_\ell(d),\qquad |y(d)|\le A_yd_\ell(d).$$

With $W=T-H$,

$$
 \boxed{|\mathcal L_B(x,y)|\le A_xA_y\mathscr K_\ell,}
$$

$$
 \mathscr K_\ell
 =4WV^2B_*(1+\log B_*)^{2\ell-2}(1+T)^{\ell^2}.
 \tag{7.4}
$$

**Proof.** Write $d=ha,e=hb$. The low mask bounds $a,b\le B_*$. After taking absolute values in this selected region, (7.2) bounds the integrand sum by

$$
 A_xA_yV^2
 \left(\sum_{a\le B_*}\frac{d_\ell(a)}{\sqrt a}\right)^2
 \sum_{h\le e^T}\frac{d_\ell(h)^2}{h}.
$$

Dropping coprimality here is legitimate because the majorant is nonnegative. Apply (7.3) and integrate for length $W$. $\square$

In the exact J17 coefficient split $v_Q=s_r+c_r$,

$$
 \begin{aligned}
 s_r&=\sum_{i=1}^r(-1)^{i-1}\binom ri
       v_{\le Y,Q}^{*i}*\mathbf1_Q^{*(i-1)},\\
 c_r&=v_{>Y,Q}^{*r}*\mathbf1_Q^{*(r-1)},
 \end{aligned}
$$

where these convolutions are Dirichlet convolutions of coefficients. Counting the contributing factorizations gives

$$|s_r(d)|\le(2^r-1)d_{2r-1}(d),\qquad |c_r(d)|\le d_{2r-1}(d).$$

Let $F=X_{v_Q}=\mathcal E+\mathcal B$, $\mathcal E=X_{s_r}$, $\mathcal B=X_{c_r}$, and $e_I=\|\mathcal E\|_{\infty,I}$. The finite native inverse coefficient bound gives $|F(t)|\le2Ve^{T/2}$ on $I$. Equation (7.1) therefore yields

$$
 \begin{aligned}
 |\mathcal Q_B(s_r,c_r)|
 &\le We_I(2Ve^{T/2}+e_I)+(2^r-1)\mathscr K_{2r-1},\\
 |\mathcal Q_B(s_r,s_r)|
 &\le We_I^2+(2^r-1)^2\mathscr K_{2r-1}.
 \end{aligned}
 \tag{7.5}
$$

More economically, $F^2-\mathcal B^2=2F\mathcal E-\mathcal E^2$ gives

$$
 \boxed{
 \left|\int_I|F|^2-\mathcal Q_B(c_r,c_r)\right|
 \le \mathscr K_{2r-1}+4We_IVe^{T/2}+We_I^2.
 }
 \tag{7.6}
$$

This proves the mask-transfer mechanism rather than inferring it from scalar cancellation alone. A small complete scalar sum can have a large masked quadratic; (7.4) is the additional arithmetic information needed here.

To assert an $e^{o(T)}$ error, the displayed parameters must actually satisfy the budget. Sufficient conditions include $\log V=o(T)$, $r^2\log(1+T)=o(T)$, $\log B_*=o(T)$ with the full $(r-1)\log(1+\log B_*)$ term also $o(T)$, and a sufficiently small $e_I$. The earlier corridor supplies a particular such schedule; fixed-parameter rapid decay is not itself a uniform moving-parameter bound. [S6, S7]

## 7.4 Theorem A3: kernel absorption has a lawful, but not literal, mask adapter

Suppose two finite-at-each-time expansions define exactly the same scalar field $F$:

$$F=X_{c,U}=X_{w,R}.$$

Let their respective low and high pair masks use their own expansion indices, with the same observation window. Then

$$
 \boxed{
 \mathcal Q_B(c,c;U)-\mathcal Q_B(w,w;R)
 =\mathcal L_B(w,w;R)-\mathcal L_B(c,c;U).
 }
 \tag{7.7}
$$

Consequently, if the two low-mask terms have independently verified subexponential budgets on a schedule, the high-mask observations have the same rates by E2.

**Proof.** Expand the same $\int_I|F|^2$ in each representation and subtract. Then apply the triangle inequality and E2. $\square$

This supplies a correct version of the proposed “absorb the unconfined factors” step. Indeed, with

$$
 N_Q=D_Q*N,\quad
 R_{d_{\rm src},r-1,Q}=N_Q^{*(r-1)}*U_{d_{\rm src},Q},
 \quad w_r=v_{>Y,Q}^{*r},
$$

local finiteness gives $X_{c_r,U}=X_{w_r,R}$. Moreover

$$
 R_{d_{\rm src},r-1,Q}
 =D_Q^{*r}*R_{d_{\rm src},r-1},
 \quad
 \|R_{d_{\rm src},r-1,Q}\|_\infty
 \le b_Q^r\|R_{d_{\rm src},r-1}\|_\infty.
 \tag{7.8}
$$

The second representation uses the bound $|w_r(d)|\le d_r(d)$, while the first uses $d_{2r-1}$. Both low-mask costs must be paid. The source-envelope schedule can be tested against these explicit costs; they cannot be inferred merely by relabeling $c_r$ as $w_r$.

For fixed $d_{\rm src}\ge r-1$, the forward kernel's elementary pole cancels, and the source papers give rapid decay. For changing orders and palettes the constants, palette-delay support and permitted time region remain part of (7.8)'s application. This regrouping is useful dependency compression, not a new signed upper for the high-primitive term.

## 7.5 What the corrected arithmetic architecture says

On the already specified paper schedule where (7.6) is subexponential and MS1 identifies the complete energy rate,

$$
 \frac{\log(1+[\mathcal Q_B(c_n,c_n)]_+)}{2T_n}\longrightarrow\Theta.
$$

This is a **conditional PAPER application** of a generic fully proved rate-comparison theorem to source-specific paper inputs. It preserves the target lower obstruction and concentrates the independent upper problem on a real signed term. That is an advantage, not a refutation of all bilinear estimates.

The narrower false claim is that the mask itself supplies cancellation or removes the coherent native channel. The complete rational-row term $q_P\mathbf1\mathbf1^*$ contributes to off-diagonal pairs as well as the diagonal. Coprimality of $a,b$ does not make the values or phases of the actual source coefficients independent. No power saving is obtained from these identities alone.

# 8. Analytic bridge: what a pole does and does not imply globally

## 8.1 Theorem B1: a genuine weighted $L^2$ bound excludes poles in its half-plane

Let $f:[0,\infty)\to\mathbb C$ be measurable and let $e^{-\epsilon t}f(t)\in L^2(0,\infty)$. Then

$$L_f(z)=\int_0^\infty e^{-zt}f(t)\,dt$$

is holomorphic on $\Re z>\epsilon$, and for every integer $j\ge0$,

$$
 |L_f^{(j)}(z)|
 \le\|e^{-\epsilon\cdot}f\|_2
 \frac{\sqrt{(2j)!}}{[2(\Re z-\epsilon)]^{j+1/2}}.
 \tag{8.1}
$$

**Proof.** For $a=\Re z-\epsilon>0$, Cauchy–Schwarz gives absolute integrability of $t^je^{-zt}f(t)$ and the stated bound, since

$$\int_0^\infty t^{2j}e^{-2at}\,dt=(2j)!/(2a)^{2j+1}.$$

On compact subsets of the half-plane, replace $a$ by a fixed positive lower bound. These majorants justify differentiation under the integral, giving holomorphy and (8.1). $\square$

If this transform has been identified on an initial nonempty open set with a meromorphic function on a connected domain contained in $\Re z>\epsilon$, uniqueness of meromorphic continuation forces that function to be holomorphic there. A genuine nonzero pole at $\lambda$ with $\Re\lambda>\epsilon$ is therefore incompatible with the weighted norm premise.

The strict inequality is essential. A pole alone does not determine an exact rate on every logarithmic window. That stronger native assertion is J5.2/MS1, with its additional source, zero-count and uniform-completion hypotheses.

## 8.2 Theorem B2: actual-input nonrange and quantitative separation

Let $A:H_1\to H_2$ be a bounded linear map between complex Hilbert spaces. Let $\ell:H_2\to\mathbb C$ be a nonzero continuous linear functional such that $\ell(Ax)=0$ for every $x$, and let $Y\in H_2$ satisfy $\ell(Y)\ne0$. Then

$$
 Y\notin\overline{\operatorname{Ran}A},
 \qquad
 \operatorname{dist}(Y,\overline{\operatorname{Ran}A})
 \ge\frac{|\ell(Y)|}{\|\ell\|}>0.
 \tag{8.2}
$$

**Proof.** Continuity makes $\ell$ vanish on the range closure. For every $z$ in that closure,

$$|\ell(Y)|=|\ell(Y-z)|\le\|\ell\|\|Y-z\|.$$

Take the infimum. $\square$

In the native project, the adjoint exponential-polynomial witness and its nonzero pairing with the **actual** completed input are already source-identified by the corresponding Lean modules. B2 explains the architecture of that obstruction. It does not create a new input-range theorem in the opposite direction. [R3–R5]

A smaller forward norm or a faster-decaying completed input does not contradict (8.2): bounded forward operators may have proper range closure. A claim of recovery has to consume the actual source and the correct damping domain.

# 9. Observation and finite-compatibility layer

## 9.1 Theorem O1: a projection must retain the target information

Let $V,W$ be finite-dimensional vector spaces, $P:V\to W$ linear, and $\ell:V\to\mathbb C$ linear. There exists a linear map $\widetilde\ell:\operatorname{Ran}P\to\mathbb C$ with

$$\ell=\widetilde\ell\circ P$$

if and only if

$$\boxed{\ker P\subset\ker\ell.}\tag{9.1}$$

**Proof.** Necessity follows by applying the identity to $v\in\ker P$. Conversely, define $\widetilde\ell(Pv)=\ell(v)$. If $Pv=Pv'$, then $v-v'\in\ker P\subset\ker\ell$, so the definition is independent of the chosen preimage. Linearity follows. $\square$

In finite dimensions this gives a finite operator-norm bound for the recovered observation. Along a changing dimension or horizon, a useful exponential-rate conclusion additionally requires that this recovery norm has subexponential cost. In infinite-dimensional settings, algebraic factorization alone does not ensure bounded recovery.

For the contrast projection $P=I-\mathbf1\mathbf1^*/d$ and the original sum observation $\ell(v)=\mathbf1^*v$,

$$P\mathbf1=0,\qquad \ell(\mathbf1)=d\ne0.$$

Thus the generic contrast cannot recover the native sum. Removing a coherent term from a Gram matrix may remove exactly the evidence needed to bound the source of interest. A separate native observability theorem is required.

## 9.2 Proposition O2: Gram kernels are not automatically rank one

For vectors $\psi_t$ and an integrable finite-dimensional Gram construction,

$$K=\int_I\psi_t\psi_t^*\,dt$$

is positive semidefinite because $v^*Kv=\int_I|\psi_t^*v|^2dt\ge0$. Its rank is the dimension of the span observed by the family, modulo null sets, not generally one.

For instance $\psi_t=(1,t)^T$ on $[0,1]$ gives

$$K=\begin{pmatrix}1&1/2\\1/2&1/3\end{pmatrix},\qquad\det K=1/12>0.$$

The same phenomenon occurs for shifted source kernels: two nonzero compact translates with disjoint supports have a diagonal positive Gram matrix on a window containing both supports. Even overlapping translates need not be proportional.

Nor does a quadratic estimate $|v^*Lv|\le C$ for one vector establish an operator-norm estimate for $L$. For example $v=(1,0)^T$ and $L=\operatorname{diag}(0,M)$ give $v^*Lv=0$ for arbitrary $M$. DC1 controls its specified coefficient class, not every unit vector. Removing diagonal matrix entries can also destroy positivity: the off-diagonal matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ has a negative eigenvalue.

## 9.3 Theorem O3: a genuine multi-frequency incompatibility certificate

Let $B:\mathbb C^d\to\mathbb C^N$ be linear. Then

$$
 b\notin\operatorname{Ran}B
 \quad\Longleftrightarrow\quad
 \exists y\in\mathbb C^N:
 B^*y=0\ \text{and}\ y^*b\ne0.
 \tag{9.2}
$$

Moreover,

$$
 \operatorname{dist}(b,\operatorname{Ran}B)
 =\sup_{\substack{B^*y=0\\\|y\|\le1}}|y^*b|.
 \tag{9.3}
$$

**Proof.** Let $P_B$ be the orthogonal projection onto the finite-dimensional closed range. The vector $r=b-P_Bb$ lies in $\ker B^*$. If $b$ is outside the range, $r\ne0$ and $r^*b=\|r\|^2\ne0$. Conversely, $b=B\alpha$ implies $y^*b=0$ whenever $B^*y=0$. For (9.3), every allowed $y$ pairs only with $r$, so Cauchy–Schwarz gives the upper bound $\|r\|$; $y=r/\|r\|$ attains it when $r\ne0$. $\square$

For a history family $H(z;\alpha)=\sum_{j=1}^d\alpha_jh_j(z)$, finitely many value or derivative evaluations define $B$. More than $d$ rows permit left-null relations, but do not prove a violated relation. If the data were obtained from the same identity $H(z;\alpha)$, they automatically equal $B\alpha$ for every number of rows.

A simple fixture is a degree-five polynomial evaluated at any seven points: seven data values are exactly consistent with its six coefficients. A true contradiction requires the second half of (9.2), established independently from the native source, not another evaluation of the identity that defined $b$.

Multiplicity jets, conjugate/reflection symmetries, parity restrictions and coincident sampling points can reduce independence. Critical-line evaluations also cannot automatically use off-line nonvanishing of a contact generator. Boundary points of transform domains require their own continuation justification. No “seven zeros beat six constants” argument is accepted without these checks.

## 9.4 Theorem O4: equivalent observations do not add constraints

Suppose a data vector $b$ is related to another observation by an invertible linear map $S$, so the compatibility equation $B\alpha=b$ is transformed to $SB\alpha=Sb$. The two systems have exactly the same solution set. More generally, left multiplication by a noninjective map can remove constraints, not create an inconsistent one that was absent in the original system.

**Proof.** Apply $S^{-1}$ for the equivalence. For a general left map, every solution of the original is still a solution of the image equation. $\square$

This gives a precise version of the warning about multiple descriptions of one residue. Multi-frequency work remains potentially useful when a global native theorem constrains the data independently, but multiplying or sampling an already exact identity does not by itself do so.

# 10. Fourier/support layer and the sharp-gap test

## 10.1 Theorem H1: the signed sharp-gap separator

Use Fourier convention $\widehat f(\xi)=\int f(x)e^{-2\pi ix\xi}dx$. Let $\nu$ be an even real locally finite signed measure with

$$
 |\nu|([-R,R])\le C(1+R),\qquad \widehat\nu=\nu\text{ in }\mathcal S',
$$

$$\nu|_{(-1,1)}=0\text{ as a measure},\qquad
  \nu|_{\mathbb R\setminus\mathbb Z}\ge0.$$

Then $\nu=0$.

**Proof.** Put $s(x)=(\sin\pi x/(\pi x))^2$, with $s(0)=1$, and $\Delta(x)=(1-|x|)_+$. The exact Fourier pair is $\widehat s=\Delta$. To justify the pairing with a non-Schwartz test, use $s_\epsilon(x)=s(x)e^{-\pi\epsilon x^2}$. Then $\widehat{s_\epsilon}=\Delta*G_\epsilon$, where $G_\epsilon(x)=\epsilon^{-1/2}e^{-\pi x^2/\epsilon}$.

The left tests are dominated by a constant times $(1+x^2)^{-1}$, integrable against $|\nu|$ by dyadic annuli. The right tests converge to the continuous triangle and, for $0<\epsilon\le1$, are bounded on $[-2,2]$ and dominated by a fixed Gaussian outside. Dominated convergence on both sides of Fourier self-duality proves

$$\int s\,d\nu=\int\Delta\,d\nu.$$

The right side vanishes by the gap; the triangle vanishes at its endpoints. The origin atom is zero, and $s$ vanishes at all other integers. Since $s>0$ away from the integers and the measure there is nonnegative, the measure is supported on $\mathbb Z$.

Write $\nu=\sum_n a_n\delta_n$. Its Fourier transform is a 1-periodic tempered distribution. Self-duality makes $\nu$ itself 1-periodic, so $a_n=a_0=0$ for every $n$. $\square$

The theorem permits arbitrary signed lattice corrections with the stated growth. It is an independent theorem about an auxiliary measure class. Its application to RH still needs an actual nonzero contact-to-measure construction satisfying every hypothesis. Spatial or nonlinear operations do not make the theorem stop applying; they can only be candidates for deriving its premises from native data. [S8]

## 10.2 Corollary H2: the global negative-mass budget

Without the off-lattice positivity assumption, let $\nu_\pm$ be the Jordan parts, and define

$$E_{R,d}=\{x:|x|\le R,\ \operatorname{dist}(x,\mathbb Z)\ge d\},
\quad R\ge1,\quad0<d\le1/2.$$

Then the same pairing equality gives

$$
 \boxed{
 \int_{\mathbb R\setminus\mathbb Z}s\,d\nu_-
 \ge\frac{4d^2}{\pi^2R^2}\nu_+(E_{R,d}).
 }
 \tag{10.1}
$$

Indeed $|\sin\pi x|\ge2d$ on $E_{R,d}$ and $|x|\le R$. The positive and negative $s$-weighted masses agree globally. An apparent sign gain on $[1,R]$ is not a violation of (10.1) unless negative mass on the entire omitted exterior has also been controlled.

## 10.3 Theorem H3: parity of a Fourier commutator

Let $\mathcal F$ be a linear involution on a common vector space $V$, let $P$ be a linear map preserving that space, and let $\mathcal F\mu=\mu$. For

$$\nu=[P,\mathcal F]\mu=P\mathcal F\mu-\mathcal FP\mu,$$

one has

$$\boxed{\mathcal F\nu=-\nu.}\tag{10.2}$$

**Proof.** Since $\mathcal F\mu=\mu$ and $\mathcal F^2=I$, $\nu=P\mu-\mathcal FP\mu$. Applying $\mathcal F$ reverses those two terms. $\square$

For Fourier transformation, use the even subspace and a well-defined even spatial operation so that $\mathcal F^2=I$. The raw commutator is anti-self-dual. Its self-dual projection $(I+\mathcal F)\nu/2$ is zero. The anticommutator $P\mu+\mathcal FP\mu$ is self-dual, but does not automatically retain the spatial gap or sign. Multiplication of an arbitrary distribution by a sharp indicator is not even a defined operation without further regularity.

## 10.4 Theorem H4: the exact Fejer/completion identity, including its correction

Let $m=\lfloor e^t\rfloor$, $u=e^t-m\in[0,1)$ and $t\ge0$. Poisson summation for the squared-sinc/triangle pair yields

$$
 \begin{aligned}
 K(t)&=2e^{t/2}\sum_{n\ge1}s(ne^t)\\
 &= (2m+1)e^{-t/2}-m(m+1)e^{-3t/2}-e^{t/2}\\
 &=u(1-u)e^{-3t/2}.
 \end{aligned}
 \tag{10.3}
$$

The native completion is $\mathfrak a(t)=m(1-u)e^{-3t/2}$, so

$$
 K=(u/m)\mathfrak a,\qquad
 K+\mathfrak a=(1-u)e^{-t/2},\qquad
 0\le K\le\tfrac14e^{-3t/2}.
 \tag{10.4}
$$

**Proof.** Poisson gives $\sum_{n\in\mathbb Z}s(ne^t)=e^{-t}\sum_{k\in\mathbb Z}\Delta(ke^{-t})$. The second sum has the finite value $1+2m-m(m+1)e^{-t}$, including a zero endpoint if $e^t$ is an integer. Remove the $n=0$ term and multiply by $e^{t/2}$ to get the first two lines. Substitute $e^t=m+u$ to get the last line and (10.4). These convergent lattice pairings can equivalently be justified by the Gaussian regularization used above. $\square$

The pointwise ratio in (10.4) does not identify two convolution operators or supply a bounded inverse. The correct transform relation is **affine**, not purely multiplicative:

$$
 \boxed{
 \widehat{\mathfrak a}(z)
 =\tfrac12(z-\tfrac12)\widehat K(z)
   +\frac1{2(z+1/2)}.
 }
 \tag{10.5}
$$

To verify it, initially for $\Re z>1/2$,

$$
 \widehat K(z)
 =\frac{2\zeta(z+1/2)}{(z+1/2)(z+3/2)}
     -\frac1{z-1/2}+\frac1{z+1/2}.
$$

Multiplication by $(z-1/2)/2$ gives the native multiplier plus the negative of the rational correction in (10.5). The true transform of $K$ extends to $\Re z>-3/2$ by (10.4), with apparent singularities treated by continuation. The common domain is retained when comparing actual transforms.

$K$ is continuous, but at $t=\log n$, $n\ge2$, its one-sided derivatives are $-1/\sqrt n$ and $+1/\sqrt n$. The claim that the derivative vanishes because every summand has a double zero interchanges an infinite sum and differentiation without uniform control. The exact formula disproves it.

The positive quantity $\int|X_j(t)|^2K(t)dt$ is not yet an RH-strength upper. The elementary coefficient estimate $\Lambda(n)\le\log n$ and fixed compact $j$ give $|X_j(t)|\le C_j(1+t)e^{t/2}$ on the causal half-line. Equation (10.4) then already makes this weighted integral finite. A weight that supplies so much decay cannot exclude every smaller hypothetical displacement just by finiteness.

## 10.5 Domain failures in the proposed noncompact measure construction

For $\mathcal D_t=e^{t/2}\operatorname{Comb}_{e^t}$, $\widehat{\mathcal D_t}=\mathcal D_{-t}$. But the weak integral

$$\int_0^\infty\phi(t)(\mathcal D_t+\mathcal D_{-t})dt$$

does not follow from $\phi\in L^1$. Comb pairings can grow like $e^{t/2}$. A simple sufficient condition is $\int_0^\infty|\phi(t)|e^{t/2}dt<\infty$; weaker conditions need their own proof. The proposed mode with $0<\delta<1/2$ decays like $e^{-\delta t}$ and fails this sufficient absolute-convergence condition. Pairing a nonnegative test supported away from zero reveals a backward-comb leading term proportional to $e^{t/2}$; the resulting growing oscillatory integral does not converge ordinarily.

The formula for a mode's Laplace transform was proved only on $\Re z>-\delta$. Substituting $z=-1/2$ and declaring its integral zero is outside that domain. Likewise $\sum n^{-\rho}$ in the strip $1/2<\Re\rho<1$ is not the convergent Dirichlet series defining $\zeta(\rho)$. A regularization would define a new object whose measure order, sign, self-duality and origin term must be checked anew.

There is also a basic sign mismatch in the first proposal. For $\lambda=\delta+i\gamma$,

$$
 2\Re[i(\lambda-1/2)e^{-\lambda t}]
 =2e^{-\delta t}[(\delta-1/2)\sin(\gamma t)-\gamma\cos(\gamma t)],
$$

not the displayed negative of both trigonometric terms. The rational Laplace formula in that note matches the complex definition rather than the incorrectly expanded sine sign. Neither expression repairs the inadmissible moment evaluation.

A square also requires the transform sign convention to be retained: for a decaying adjoint mode $\psi=e^{-\lambda t}$, $|\psi|^2=e^{-2\delta t}$ has a Laplace pole at $z=-2\delta$, not $+2\delta$. A growing mode has the opposite sign, but its growth cannot be substituted for the adjoint's decay. A real argument equal to the pole $s=1$ is not an ordinary finite nonzero value of zeta.

For a causal shift $\phi_D(t)=\sum_k a_kk^{-1/2}\phi(t-\log k)\mathbf1_{t\ge\log k}$, the transform multiplier is $D(z+1/2)$. At $z=1/2-s$, it is $D(1-s)$, not $D(s)$.

The attached executable is only the initial 31-line integer-sample test. Its Fourier cutoff is closed $[-1,1]$, not compactly contained in $(-1,1)$, and its endpoint regularity is $C^1$ rather than a smooth bump. The six small floating-point values neither prove all integer zeros nor execute the rest of the pasted derivations. The file was run successfully here; that exact scope is recorded separately.

# 11. What the architecture says about the four proposed exits

## 11.1 Multi-zero/contact compatibility

This remains a legitimate research lead. Its minimal meaningful mathematical output is a source-derived compatibility residual as in O3, not a count of spectral samples. The contact source, its polarized observation, the ordinary completion, and its compact history must stay distinct. The left and right tails, conjugate zeros and multiple derivatives can be coupled only through identities valid on their actual domains.

A finite test should first build the actual matrix of boundary evaluations, determine its rank after symmetry constraints, and derive the data independently. If every proposed data row is just the same exact exterior identity evaluated again, its residual is identically zero and no new constraint has entered. If an independent global identity gives a nonzero left-null pairing, then O3 provides a genuine contradiction. The latter step is OPEN.

The six-dimensional normal family is not a free reservoir of six adjustable constants: its values are already fixed by the source. Conversely, the source being fixed does not make the infinitely many identities inconsistent. Both facts must be respected.

## 11.2 Genuine signed bilinear dispersion

The corrected native high-mask term is a meaningful target. A2 removes controlled low-primitive terms, and A3 allows absorption of unconfined factors with separately priced comparison errors. Neither result makes the surviving coefficients independent or their kernel low-rank in a useful operator-norm sense.

The useful next assertion must exhibit a strictly improved *complete* signed bound from an actual arithmetic property. Its proof must retain repeated-prime tuples, the exact common-gcd range, the observation kernel and its source-dependent localization, and all coherent character rows. A sum/product factorization, a convergent Euler factor at a sum frequency, or a formal two-variable Mellin integral is not such a bound by itself. The previously computed genuine conjugate Euler numerator is strictly positive rather than a pole-cancelling factor; that historical result must be tested against any claimed sieve cancellation. [S1, S7]

Preservation of the hypothetical lower obstruction does not refute this target. A successful independent upper would contradict the lower. What is refuted is the inference that changing to the mask automatically supplies the upper.

## 11.3 Character contrasts

A contrast can eliminate a rank-one coherent channel exactly. O1 asks the necessary accompanying question: can the original field still be recovered or bounded from the contrast observations, at an acceptable cost? If not, the new statistic may be small while saying nothing about the field we are trying to control.

The row and column spaces of the Gram construction must be named before choosing an orthogonal vector. A projection on observation rows is not interchangeable with a projection on arithmetic coefficient columns. No theorem is supplied here that transfers a bound for a contrast of twisted $L$-function observations back to the literal zeta prime field. That bridge is OPEN.

## 11.4 Spatial heat-defect constructions

The signed separator is independent auxiliary mathematics, but every admissible map must satisfy its complete hypotheses. The elementary commutator fails the self-duality requirement by H3. Its self-dual symmetrization is zero, while an anticommutator loses automatic gap control. Nonlinear or spatial constructions are not thereby impossible; they need a genuinely source-derived measure, with its atomic part, off-lattice part, support, Fourier transform and total variation calculated before any positivity claim.

The signed separator's pairing identity applies to all measures satisfying its assumptions, regardless of how they were constructed. A new construction cannot “escape” that identity. It can only use the identity to contradict a hypothetical source state after independently deriving all the incompatible properties. This native construction remains OPEN.

## 11.5 No universal necessity claim

It has not been proved that a successful RH argument must couple different zeros, be nonlinear, subtract a rank-one channel, or leave every class of linear operators. A global inequality, domain theorem, or arithmetic positivity result could act on an existing linear representation and still provide exactly the missing independent information.

OPICA's actual exclusion statements are limited: specified transforms preserve a specified local class; specified perturbations preserve a specified observed rate; and specified projections cannot recover a target they annihilate. The paper does not extrapolate them into a theorem about all future mathematical discovery.

# 12. Lean construction contract for the next message

## 12.1 No repository implementation in this step

No new `.lean` file, Git commit, branch, PR, CI workflow or registry promotion was created. Source snapshots in the evidence package are read-only copies of the existing repository and historical papers. The proposed module names below do not yet exist in the checked repository.

The next implementation should retain the pinned toolchain unless an explicitly reviewed migration is separately authorized. Current online Mathlib documentation confirms the relevant analytic/meromorphic order concepts, but it is not a promise that every current API name exists at the pinned revision. Existing project proofs already demonstrate usable `AnalyticAt`, `analyticOrderAt`, `analyticOrderAt_mul`, `analyticOrderAt_comp_of_deriv_ne_zero`, and iterated-derivative APIs. Pin-specific checks must precede implementation. [R2–R5; W1–W3]

## 12.2 Implement witnesses before building a large germ library

The paper uses germs for conceptual clarity. The minimal Lean implementation can avoid introducing a complete local-ring quotient library at the outset.

A `SimplePoleData`-style structure can contain:

- a center `lambda : Complex`;
- a nonzero residue `R : Complex`;
- an analytic remainder `h` at that center;
- equality of the proposed meromorphic expression with `R / (z-lambda) + h z` on a **punctured neighborhood**.

A `MultiplierOrderData`-style structure can contain:

- an order `k : Nat`;
- an analytic unit representative `u` with `u lambda != 0`;
- a genuine-neighborhood identity `M z = (z-lambda)^k * u z`.

For `k >= 1`, define the regular representative explicitly as

$$g(z)=(z-\lambda)^{k-1}u(z)[R+(z-\lambda)h(z)].$$

Prove its analyticity, derivative vanishing and leading derivative. Do not define it by arbitrary totalized division at the center and then assume that representative is analytic there.

For energy, use schedules and the finite real logarithmic inequality E1. A generic predicate `SubexpAlong T u` should mean the explicit limit in Section 5, with $T_n>0$ and $T_n\to\infty$ supplied where needed. It must not be a postulated property of the native prime field. The full-rate theorem is a separate hypothesis in generic comparison lemmas; a native J5.2/MS1 instantiation must retain its not-yet-formalized status until actually proved.

## 12.3 Proposed module and declaration map

All proposed modules live under `Zeta23/OPICA/`. Exact suggested declaration names are recorded in the separate implementation contract and theorem ledger.

| Module basename | Paper content | Public interface family |
|---|---|---|
| `LocalObstruction` | L1–L3 | Unit residues, completed jets, residual congruence and repeated completions |
| `AffineTransport` | L4 | Exact correction ledger, total order and raw-cancellation fixture |
| `EnergyRate` | E1–E3 | Log comparison, subexponential errors and tempered scales |
| `Composition` | E4–E5, C1–C2 | Accumulated budget, quotient faithfulness and cofinal-rate consumer |
| `ObservationCompatibility` | O1–O4 | Recovery criterion, left-null certificates and exact counterexamples |
| `NativeJetAdapter` | Existing native jets | Source-bound actual-input/kernel adapters with visible damping and multiplicity |
| `DivisorMask` | A1–A3 | Divisor bounds, low-primitive bilinear estimate and regrouped-mask comparison |
| `FourierCompatibility` | H1–H4 | Involution sign, signed separator and fully corrected Fejer identity |
| `Validation` | Exact roots | Aggregate consumer, declaration types and axiom prints |

These are proposed names and boundaries, not claims of compilation. The algebraic involution lemma from H3 can be implemented before the measure theory in H1. The quotient/Taylor equivalence (4.4) can be formalized as a separate representation theorem after the explicit leading-jet lemmas. The exact integral version of A2 requires its finite-sum/source-support interface, not just a theorem about an abstract majorant.

## 12.4 Existing native declarations to reuse, not re-postulate

The pinned source contains the following relevant names:

- `nativeZeroMultiplicity_order` and `nativeZeroMultiplicity_deriv_order`;
- `nativeZeroJetKernelMultiplier_order` and `nativeZeroJetInputMultiplier_order`;
- `nativeZeroJetInputMultiplier_jet` and `nativeZeroJetSourceFactor_ne_zero`;
- `nativeActualInputLaplace_eventuallyEq_multiplier` and `nativeActualInputLaplace_order_of_zero`;
- `nativeCompletedInput_zeroJet_value` and `nativeCompletedInput_zeroJet_ne_zero`;
- the actual kernel moment and adjoint-kernel declarations in `NativeActualKernelZeroJets.lean`;
- the three explicitly conditional cuts in `Step4OutputSufficiency.lean`.

The two actual-transform modules distinguish analytic formulas from the physical integrals. Their neighborhood equalities are precisely the interface OPICA needs. Do not replace them with a new caller premise asserting the desired native nonzero jet, source visibility, or prime-field membership.

The original constrained-contact paper is not present as a fully compiled C05 theorem suite on the audited scope. An OPICA contact application must therefore remain a clearly labelled paper adapter or a theorem conditional on explicit mathematical hypotheses until those source theorems are formalized. It must not be smuggled into the native producer as an axiom.

## 12.5 Dependency and acceptance order

**Core first.** Implement local leading-jet algebra, correction composition, elementary log comparison, finite-chain propagation, projection/compatibility algebra and exact counterexamples. These do not need the conjecture or an independent Step 4 upper.

**Native binding second.** Instantiate the local laws using the existing source-specific zero/kernel/input declarations, checking the precise right-zero choice, damping shift and source. The result should explain the already proved nonzero input jet, not claim a new native upper.

**Analytical extensions third.** Formalize the low-mask integral, Fourier separator and any J5.2/MS1 native rate instance only with all their analytic dependencies. Generic rate lemmas may compile earlier with a stated rate-limit hypothesis; that is not a compiled proof of the native hypothesis.

**Required gates.** For every promoted root, record the exact Git SHA and tree, full declaration type, imports, assumption closure and `#print axioms`. No `sorry`, `admit`, new project axiom or hidden RH-equivalent premise is permitted. The gate must distinguish ordinary kernel-checked evaluation from trust extensions such as native compiler evaluation. Compile the actual consumer modules, not merely a new definition with no native use.

The existing `.github/workflows/rhrc_post290_step123_output.yml` names implemented components explicitly. The next PR should either add the new component list through the reviewed integration process or supply a separately pinned OPICA workflow with its own exact receipts. It must not silently change the historical 44-field acceptance contract, semantic approval rules, D2 state or existing Step 4 claim caps.

A compiled theorem with a new false axiom would not prove its conclusion. Lean tracks axiom dependencies, but does not establish the truth of newly postulated axioms. This is why the dependency inventory is part of acceptance, not a cosmetic report. [W3]

## 12.6 What success in the next message would and would not mean

A successful first OPICA implementation would formally establish the requested preservation architecture's core and source-bound jet adapters at their exact scopes. It would also formalize the relevant counterexamples to the overly broad proposals. That is a useful new theorem package.

It would **not** establish A-X, B-Y, C-Schur, OPEN-J46, native contact-to-heat positivity, or RH merely because the architecture compiles. The independent-constraint layer records the exact location where new mathematics must enter. That layer may have generic implication lemmas, but no supplied native closing certificate in this paper.

# 13. Validation, adversarial tests and post-result research pass

## 13.1 Executed finite controls

The included standard-library checker `checks/check_opica.py` completed **5,112 exact assertions**. The groups cover finite Laurent-polynomial residue/jet identities, repeated-completion factorials, affine correction recursion, the algebraic inequalities underlying logarithmic comparison, accumulated budgets, divisor bounds, repeated-prime mask fixtures, Gram/projection and finite-compatibility counterexamples, Fourier involution parity, and rational Fejer/completion identities.

These are finite rational, polynomial and combinatorial checks. Their value is to catch sign, factorial, mask and indexing mistakes. They do not prove analytic continuation, infinite limits, signed-measure convergence, J5.2/MS1, or RH. The written arguments in this paper carry those claimed mathematical conclusions at PAPER authority.

The supplied 31-line numerical script was also executed unchanged. It printed the six near-zero Fourier samples from the submitted transcript. This is a successful replay of that narrow numerical experiment, not a test of the later heat-measure or contact-jet assertions. Its stdout/stderr and byte hash are retained. No other pasted notebook output is promoted to a fresh executed result.

No Lean executable was present on the runtime path, and this step did not install or run Lean. No GitHub source or workflow was changed. The repository check consists of the live reference/tree/PR observations and the three matched source blobs described in Section 1. The detailed historical CI dispositions remain historical.

## 13.2 Adversarial mathematical checks

The paper explicitly treats $m=1$, higher multiplicities, zero and nonzero multiplier order, arbitrary analytic backgrounds, the difference between derivatives and coefficients, and the failure of unrestricted infinite composition. It retains $\Theta=0$ as well as $\Theta>0$, negative signed energy remainders, inverse scaling costs, changing horizons, and accumulated additive errors. The arithmetic check retains $a=1$, repeated primes and common-gcd overlap, and separates the old and regrouped masks. The Fourier check includes endpoint atoms, a global rather than truncated negative-mass budget, measure versus distribution status, and the anti-self-dual sign of the commutator.

The mathematically important correction discovered by the source reread is not an optional notation change: M0608's $\kappa_{\rm obs}$ and the completion $\mathfrak a$ have different zero orders at the hypothetical zero. Identifying them changes the first nonzero jet and invalidates the proposed proof. The historical real-zero simplicity question also has a later source-specific repair; the paper uses that provenance rather than keeping the earlier gap permanently open.

The blanket phrase “universal no-go theorem” is not adopted. Nor are the four candidates called “barrier-free.” The architecture has exact positive preservation results and exact scope limitations. It is a theorem package plus an audit interface, not a theorem that RH is unreachable by some broad informal category of reasoning.

## 13.3 What became mathematically available

**Formally true this turn:** no new Lean declaration. The new output is a paper proof package with separately executed finite controls.

**Workflow harvest:** the new finite checker passed with its stated scope; the submitted six-sample numerical script replayed; live source identity checks matched. No formal-validity gate ran. No unknown CI job was treated as passed, and no new research run was represented as a native RH restriction.

**What changed:** local pole/jet transport now has exact carrier spaces, correction-aware composition and leading coefficients. Observed energy preservation is formulated without false rank or eigenvalue claims. The two contact kernels are separated. Projection and compatibility routes have precise tests for lost information and genuine inconsistency. Kernel absorption has a lawful two-mask adapter rather than an invalid identity.

**Upstream implications:** source and observation types should be made explicit in theorem interfaces. Boundary terms must be classified by the target quotient, not just by whether they are entire. Fixed-stage constants and finite source identities need separate limits when parameters move.

**Downstream implications:** a new arithmetic, contact or range estimate can now be attached to an exact contradiction consumer without confusing it with a preservation edge. Failed proposals can be screened using L4, O1, O3 and H3 before expensive integration work.

**Resurrected routes:** actual signed high-primitive arithmetic survives the mask audit; its lower-obstruction preservation is useful. Multi-zero contact is meaningful only with independently derived incompatible data. Spatial heat construction remains a lead after the raw commutator fails self-duality. None is automatically closed or permanently ruled out.

**New RH-relevant clue:** the useful shared structure is preservation of a declared quotient class or observed rate under source-correct maps. It is not a single proved universal conserved scalar. This distinction may identify exactly which native premise a proposed global incompatibility uses and which synthetic controls fail to retain it.

**Fast falsifiers:** compute the actual multiplier order and correction; test the projection on the target vector; determine the true compatibility-matrix rank; include repeated-prime pairs; check measure existence before using positivity; and price the total schedule before invoking a limit.

**Highest-leverage next moves:** implement and audit the scoped core in Lean as requested, then require a candidate closing mechanism to provide a genuinely independent native separation witness or smaller complete growth rate. Tightening a cost already of zero exponential rate is not automatically information about the remaining signed term.

# 14. Source register and reproducibility

The references below identify actual source records, not assertions that every older statement is current-head theorem authority. Historical local paths are preserved only inside the source manifests where useful; all user-facing navigation uses the exact Drive or repository item.

## Repository sources

**R1. Live source state and PR metadata.**
[Main reference](https://api.github.com/repos/HMarcusWH/zeta-23-lean/git/ref/heads/main),
[pinned commit](https://github.com/HMarcusWH/zeta-23-lean/commit/97926d6a949fed7af0429a373b47abc772012834),
[PR #292](https://github.com/HMarcusWH/zeta-23-lean/pull/292).
Fresh metadata/tree observation; detailed older CI/axiom evidence is inherited.

**R2. Native analytic factors.**
[`NativeZeroJetAnalyticFactors.lean`](https://github.com/HMarcusWH/zeta-23-lean/blob/97926d6a949fed7af0429a373b47abc772012834/Zeta23/ExceptionalZero/NativeZeroJetAnalyticFactors.lean).
Fresh live blob matched `3478c3ad8268b312772fba5f68667c2a3c67b1ff`.

**R3. Actual physical input jets.**
[`NativeActualInputZeroJets.lean`](https://github.com/HMarcusWH/zeta-23-lean/blob/97926d6a949fed7af0429a373b47abc772012834/Zeta23/ExceptionalZero/NativeActualInputZeroJets.lean).
Fresh live blob matched `82ccdf1a050d82c6a262e0264b61db66b56c37df`.

**R4. Actual kernel/range witnesses.**
[`NativeActualKernelZeroJets.lean`](https://github.com/HMarcusWH/zeta-23-lean/blob/97926d6a949fed7af0429a373b47abc772012834/Zeta23/ExceptionalZero/NativeActualKernelZeroJets.lean),
[`NativeRangeZeroJetObstruction.lean`](https://github.com/HMarcusWH/zeta-23-lean/blob/97926d6a949fed7af0429a373b47abc772012834/Zeta23/ExceptionalZero/NativeRangeZeroJetObstruction.lean).
Read from the frozen repository snapshot; source pin and historical compiler status retained.

**R5. Physical completion and terminal cuts.**
[`NativeCompletedInputZetaLaplace.lean`](https://github.com/HMarcusWH/zeta-23-lean/blob/97926d6a949fed7af0429a373b47abc772012834/Zeta23/CCM/NativeCompletedInputZetaLaplace.lean),
[`Step4OutputSufficiency.lean`](https://github.com/HMarcusWH/zeta-23-lean/blob/97926d6a949fed7af0429a373b47abc772012834/Zeta23/ExceptionalZero/Step4OutputSufficiency.lean).
The latter live blob matched `88df03fc6a3ee762ec396f932c27f62c2217bc60`.

**R6. Existing output and integration contract.**
[`Step123CompleteOutput.lean`](https://github.com/HMarcusWH/zeta-23-lean/blob/97926d6a949fed7af0429a373b47abc772012834/Zeta23/ExceptionalZero/Step123CompleteOutput.lean),
[`STEP4_CUTS.json`](https://github.com/HMarcusWH/zeta-23-lean/blob/97926d6a949fed7af0429a373b47abc772012834/research/RHRC/integration/post290/STEP4_CUTS.json), and
[`rhrc_post290_step123_output.yml`](https://github.com/HMarcusWH/zeta-23-lean/blob/97926d6a949fed7af0429a373b47abc772012834/.github/workflows/rhrc_post290_step123_output.yml).
These preserve source typing, explicitly open cuts and the distinction between component compilation and full acceptance.

## Project and Drive sources

**S1. Complete session learned state, 20 October 2026.**
[Markdown](https://drive.google.com/file/d/1_Ci8DcO5acf7kTeJvAqMkqaczHNG1NYb/view), especially §§4–6, 10–13 and 17. Fresh full raw read matched the archived hash. This is a synthesis, not a replacement for the original proofs.

**S2. Full post-PR292 reassessment and joint evidence.**
[Reassessment Markdown](https://drive.google.com/file/d/1KAEhlobyVRBXXYNIz3GDGk3MOhoIZ8hu/view),
[joint evidence Markdown](https://drive.google.com/file/d/1dVuB7DeCpLvLWbuwIQskQiv6bIHXRV67/view),
[joint source ZIP](https://drive.google.com/file/d/19k2BpEf8xihPoRyvIm39bZFh0WGQfpTD/view).
The source archive is in the [third-party handover folder](https://drive.google.com/drive/folders/14VFXyGxyzf4HYWDYwkiV26oPPUmx640O).

**S3. M0608, `birds_eye.md`, 14 October 2026.** Original text recovered from the source package and directly cross-read on physical handover pages 8534–8539. Section 3 repairs constrained-generator real-root simplicity. Section 4 defines the compact probe, retained normal history and source-specific residue adapters. This source resolves the disputed meaning of $\kappa$.

**S4. M1152, `RH_PR292_Hybrid_Research_2026-10-14_RESEARCH_NOTE.md`.** Original §6, especially the compact inverse and six-dimensional interior family. Older component compiler evidence belongs to its historical tree, not to a fresh native contact theorem.

**S5. M0659, `continuation_native_j.md`; M1196, `round4_energy.md`.** The fixed-source J4.1/J5.2/J7/J8 arguments, complete factor bookkeeping and the explicit OPEN-J46 target. Physical handover navigation: approximately 8768–8781 and 11736–11745. PAPER authority retained.

**S6. Divisor-controlled mask and moving-source continuation.**
[Current Google Doc](https://docs.google.com/document/d/1KcUovuIEsqhmJ25Yqn3U-ItDmLVEVRJx-_Ltpp_CYTA/edit).
Fresh raw text export read. Its DC1/DC2 are rederived here in A1–A2. Its source-uniform MS1 remains a separate paper-level application premise, not a fresh Lean theorem.

**S7. Corridor and final-gap audits.**
[Scheduled corridor](https://drive.google.com/file/d/1NiNy6FGisx82ilHtIFrlGske8mtdkMt-/view),
[final residual/handoff audit](https://drive.google.com/file/d/1eO_QNnwswL_VzTjIgbWGgk0MUQLYIiEW/view).
Terminal-boundary transfer, exact residual multiplier and coherent-row limitations.

**S8. Heat/support sources.**
[Structural pivot](https://drive.google.com/file/d/1F1Ae0USXq0p0obiMDj6yitWaYsa6iXwb/view),
[source/check ZIP](https://drive.google.com/file/d/1Q_VwEYeg09wYL-9Wgq50bnOeRFjKjqk7/view), plus M0500 `35--08_sharp_heat_gap_rigidity--75e8016f19.md`, handover pages 8035–8037. M0632 supplies the scoped modified-prime contact/exterior control.

**S9. Project controls.** `RH Project README and Operating Rules.docx`, `RH Toolkit Ledger v0.1.docx`, and `RH_Evolving_Canvas_SSOT_v1_0_2026_06_19.docx`. Extracted text is retained in the evidence packet. Architecture is a research tool, not automatic proof authority.

**N1–N6. Submitted proposal chain.** The six timestamped text notes ending in `211411`, `212153`, `213021`, `213143`, `213916`, and `214619`, and `gemini-code-1792531343563.py`. They are preserved as received. Their overclaims, notation changes and exploratory intermediate calculations are not treated as established inputs. This paper's correction table and audit JSON identify their relevant dispositions.

## External primary documentation

**W1.** [Mathlib analytic order documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Analytic/Order.html).
**W2.** [Mathlib meromorphic order documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Meromorphic/Order.html).
The current documentation is API orientation; the implementation must use the pinned dependency actually installed in the repository.

**W3.** [Lean language reference: axioms](https://lean-lang.org/doc/reference/latest/Axioms/). Axioms are postulated constants, and `#print axioms`/dependency auditing does not itself prove new assumptions true.

## Reproduction and package boundaries

Run `python checks/check_opica.py` from the extracted evidence packet to reproduce the exact finite assertions. The result file binds the checker by SHA-256. The source index binds copied bodies and identifies whether their status is live-read, archived, source-derived or proposed. The paper's PDF is a rendering of the Markdown, not an additional independent mathematical review.

All authenticated temporary download URLs are excluded from release files. Source or paper hash matches show identity only. Release records distinguish local validation, Drive upload success and complete remote-byte readback.

# 15. Final mathematical state

The requested paper construction now has three proven-on-paper components:

1. **A source-typed local calculus** for residues, zero ideals, transferred Taylor jets, affine backgrounds and finite composition.
2. **An observation-rate calculus** for exact masks, subexponential errors, tempered scaling and fully accumulated schedules, with a separate analytic bridge to the native system.
3. **Independent-constraint tests** for observability, multi-frequency compatibility and Fourier/support separation, including explicit counterexamples to the supposed automatic escapes.

The architecture does not assert a universal obstruction to proving RH. It identifies what specified manipulations preserve and prevents them from being mistaken for a new native restriction. A future closing theorem can operate inside an existing representation if it supplies the genuinely missing independent information.

**Step 1 is complete at PAPER/DERIVED authority. Step 2 is the repository implementation and exact compiler/axiom audit requested for the next message. No Step 4 antecedent has been established by this construction. RH and Step 4 remain OPEN.**

# Riemann project handover — 2 November 2026

**RH and Step 4 remain OPEN.** The strongest recent progress is a reduction to two explicit native scalar energies at Fourier cutoff $K=3$, a separately compiled positive Archimedean comparison for that actual pair, and an unconditional signed calculation of the entire higher-prime-power sector. The remaining ordinary-prime compensation has not been bounded at the required scale. Several plausible joint-response arguments have now been tested against the actual source and fail for precise, recorded reasons.

**Where authority stands.** The research baseline is PR #299, commit `7bae463361264a0694b4fb2e9107dc4314163b33`, tree `ceffa523d3b9422a63512022cf62b5ec8ffb5784`. The latest completed baseline harvest records 24 successful workflow runs, 97 jobs: 95 successful and two declared optional skips. Their scopes differ: current Round 4 validity/compatibility, historical regression, finite numerical controls and research-producing checks. The current production inventory is 1,079 declarations in 90 modules with 84 intended type-error controls. Historical 775-root replay is not additional current theorem authority; full-release human review was not established by workflow success.

Six external Lean files supporting the actual K3 Arch comparison contain 35 public declarations: nine definitions and 26 theorems. Their pinned local compilations, expanded types, axiom audits, import bindings and reviews passed. They are **PROVED within those external receipts**, separate from the baseline production inventory. The final canonical comparison assumes only $L>0$. Its exact minus signs matter: the canonical source subtracts `canonicalArchMatrix`. The older six margin, four moment and one composed quartic results were already integrated at `95bf`; their scratch copies are historical proof evidence. The arbitrary-prescribed-margin prototype remains separately external. Consult the publication inventory before counting anything twice.

Use **PROVED** only for exact checked Lean statements; **DERIVED** for the reviewed analysis below; **FALSIFIED** for the particular rejected inference, not for the entire OPICA system; and **LEAD** for a proposed next argument. Exact symbolic checks certify their listed finite identities, not an infinite signed estimate.

**The actual two-scalar problem.** Put $\beta=L^2/(16\pi^2)$. On $n=-3,\ldots,3$, the native vectors are

\[
u_{e,n}=(\beta+n^2)(1,-6,15,-20,15,-6,1)_n,\qquad
u_{o,n}=(\beta+n^2)(-1,4,-5,0,5,-4,1)_n.
\]

They satisfy the genuine pole and endpoint constraints, with the full inherited metric. Their squared norms and index relation are

\[
N_e=924\beta^2+1512\beta+1764,\quad
N_o=84\beta^2+392\beta+724,\quad n u_e=3u_o.
\]

Write $Q_e,Q_o$ for their complete raw canonical energies, $a=N_o/N_e$, and $G=Q_o-aQ_e$. Both carriers are one-dimensional at $K=3$; their ground eigenvalues are $Q_p/N_p$. The corrected native source relation is exactly $G=80\operatorname{Re}f_{\rm source}(u_e)$. It records the same gap rather than providing an independently signed quantity. Raw and unit-normalized energies must not be interchanged.

The **DERIVED fixed-K3 Landau argument** retains all actual zeros, multiplicities, reflected partners, and the constant channel. An off-line zero forces each parity separately to have positive and negative excursions at arbitrarily large apertures. Their exponential rate is the actual supremum $\Theta\in[0,1/2]$ of rightward zero displacement; no globally rightmost zero is assumed. Thus an independently proved eventual polynomial lower bound on either literal $Q_p$ would be decisive through this reduction. That lower bound and the formal end-to-end reduction are not proved. Separate parity excursions do not establish simultaneous negativity at one aperture.

The S4-E4 attachment and the later gamma–prime attachment were fully reviewed. Their actual normalization, source covariance and finite identities are useful; neither attachment closes Step 4. In particular, the K3 vectors do **not** inherit the extra moment-zero rows of separate quartic witnesses. The latter cannot be substituted into the K3 equations.

**The positive pieces and the remaining signed arithmetic.** For $E_p(L,\theta)=\operatorname{Re}\langle u_p,S_\theta u_p\rangle$, define

\[
k_L(t)=E_o(L,1-t/L)-aE_e(L,1-t/L),\quad d_0=\frac{175}{88\pi^2}.
\]

The complete decomposition is

\[
G=A_\Gamma+B_1+B_{\ge2},\qquad
B_1=-\sum_{p\le e^L}\frac{\log p}{\sqrt p}\,k_L(\log p).
\]

Here $B_{\ge2}$ includes **every** $p^r$, $r\ge2$, with weight $(\log p)p^{-r/2}$, never $r\log p$. The locally compiled result proves $A_\Gamma(L)>0$ for every $L>0$. It uses the actual physical Fourier density and strict increase of the gamma multiplier in squared frequency. The separate derived asymptotic is $A_\Gamma=d_0 I_2L^2+O(1)$, where $I_2=7\zeta(3)+\pi^3/4$.

Exact source integration gives $\int_0^L k_L(t)\,dt=-400a\beta^2L$. Combining it with actual prime Mertens summation yields

\[
B_{\ge2}=200a\beta^2L+d_0H_2L^2+O(1),\qquad
B_{\ge2}\sim\frac{25}{352\pi^4}L^5>0.
\]

$H_2=T_2-8M_1$ is a fixed, explicitly defined signed arithmetic constant. The fine $L^2+O(1)$ expansion uses classical quantitative PNT. A useful dependency improvement was then found: the leading positive $L^5$ sector and an explicit coarse eventual threshold need only the existing unconditional theorem `Mertens.sum_mangoldt_div_eq_log`, source variation and convergent higher-power moments. The current-tree compiler coverage of that old Mertens theorem was recovered and checked. The new composition remains DERIVED.

Keep the rational factor $a(L)$ exactly: replacing it by $1/11$ leaves an $L^3$ term. The precise ordinary-prime remainder is

\[
\mathcal E_{\rm ord}=B_1+200a\beta^2L+d_0(H_2+16)L^2,
\quad
G=J_{\rm det}+\mathcal E_{\rm ord}+r_{\rm hp}-r_h,
\]

where both displayed remainders are bounded and

\[
J_{\rm det}=A_\Gamma+\int_0^L e^{-t/2}k_L(t)dt>0,
\qquad J_{\rm det}=d_0(I_2-16)L^2+O(1).
\]

Equivalently, with $R(t)=\psi(e^t)-e^t$, the unknown signed part is $\int_0^L R(t)[e^{-t/2}k_L(t)]'\,dt$, with the exact bounded compensation above. All lower prefixes and upper atoms are included. Prime counting instead of von Mangoldt counting reconstructs this same quantity. The paid PNT bound still has scale $L^{-7}e^{L/2-c\sqrt L}$. Both actual-kernel absolute-envelope methods attain that scale with a positive limiting constant; this is a limitation of those methods, not a lower bound on the true signed error.

Do not seek a fixed fractional saving against the positive sector: under RH, $G=O(L^{-7})$, so $B_1/(A_\Gamma+B_{\ge2})\to-1$. An eventual bound $B_1\ge-\kappa(A_\Gamma+B_{\ge2})$ with fixed $\kappa<1$ is therefore too strong, even in the RH case.

**What aperture coupling really supplies.** At fixed $L$, $E_e''(\theta)=-36\pi^2E_o(\theta)$. This is a source-coordinate derivative, not an aperture derivative. With

\[
X_e=\frac{L^9Q_e}{720^2(2\pi)^8},\qquad
X_o=\frac{L^7Q_o}{240^2(2\pi)^6},
\]

the aperture equation is $X_e''+X_o=F$, with a complete nonzero arithmetic forcing. At each actual prime-power seam $L=\log q$, its tenth derivative jumps by $-896\pi^2\Lambda(q)/(\sqrt q(\log q)^3)$. Actual prime powers give both signs of individual forcing terms arbitrarily late. These facts reject a homogeneous smooth ODE or eventual termwise-sign shortcut; they do not sign the full forcing. The corrected expanded forcing coefficient is **38** times $\beta E_\beta$, not 34. The superseded transcription is preserved; use the corrected `3129e82` note.

The newest same-source calculation goes further than the atom tests. Fix one $L_0$, set $P(L)=\int_{L_0}^L X_e(t)\,dt$, and retain the actual constant $C_2=2\sum_\rho m_\rho p^2b(p)$, where $p=\rho-1/2$, $b(p)=(1/4-p^2)^2/p^{14}$. Under an off-line zero, $\Theta>0$, uniform complete-zero estimates give

\[
F=C_2+448\pi^2L^{-3}P+R,\qquad
|R|\le A L^{-2}+B e^{\Theta L}L^{-4}.
\]

Constants are fixed before choosing a well and may depend on $\Theta$. On a bounded negative well $[A_0,B_0]$, put $w=-X_e>0$ and $\mathcal H=224\pi^2L^{-3}P^2$. Then

\[
\int wF=C_2\int w+\mathcal H(A_0)-\mathcal H(B_0)
-672\pi^2\int L^{-4}P^2+\int wR.
\]

This exposes a favorable bulk and improves the remaining exponential allowance by one aperture power. It also exposes the unpaid history entering the well. Summing wells leaves replenishment across the intervening intervals. Restarting $P$ at each well is invalid. The zero ordinate gap is not a Fourier gap for the actual restricted positive weight $w$: its Fourier transform at zero is positive. Damping retains a width-dependent Poincaré cost, not a free ordinate-gap estimate.

First contact gives a one-sided crossing sign, not stationarity. Global minimality of native cutoff gives all-aperture predecessor positivity, but at K3 the K2 predecessor is zero. Historical boundary-flat or fixed-aperture “global first bad” results cannot supply a missing moving-native stationarity premise. The current joint-ground constraints retain strict-even, reciprocal strict-odd and tied/full-complement branches, and require their exact same-state hypotheses.

**A full generated-prime-square shortcut is now falsified.** For the actual even physical input $f$, let $c=L^2/(36\pi^2)$, $\mathcal Q(h)=c\|h'\|^2-a\|h\|^2$, and use advance translations $T_t h(x)=h(x+t)$. The complete ordinary-prime operator is $A_L=\sum_{p\le e^L}(\log p)/\sqrt p\,T_{\log p}$. The new unconditional DERIVED result is

\[
\frac{\mathcal Q(A_Lf)}{L^2e^L}\longrightarrow-\frac{350}{11\pi^2}.
\]

It retains every distinct prime pair and the exactly zero diagonal. It is not an arbitrary-coefficient counterexample. The compact half-pole primitive $g'+g/2=f$ gives $A_{0,L}f=e^{L/2}T_Lg-g$. The large negative quadratic contribution lies outside the original input window and is orthogonal to $f$. The original linear response is still $B_1=\mathcal Q(g)-2\operatorname{Re}\mathcal B(f,(A_L-A_{0,L})f)$. Thus this falsifies the proposed full generated-history Rayleigh inequality, while leaving the closing signed cross term unpaid. Product shifts from Selberg convolution and ratio shifts from $A_L^*A_L$ must not be identified.

**Lessons from the earlier joint-system work.** Exact deconvolution, mixed cut differences and whole-response injectivity identify source coefficients; their inverse/conditioning costs do not imply a signed bound. Fixed finite cutoffs and the native moving-cutoff path have different quantifiers. Fixed-cutoff hyperbola algebra and Gevrey decay genuinely widen the negligible-prefix range, but retain the complete long Möbius tail, positive rank-one square, diagonals and boundary compensation. Low primitive sectors have useful bounded cutloads; the growing high-primitive sector remains.

For the literal $H=\kappa*\kappa$, the causal prime response $P_H$ and full echo $S=P_H*P_H$ have exact Möbius/hyperbola and reflection-energy bridges. The two internal native cutoffs remain separate, and rapid late short history does not make a mixed convolution rapid. A subexponential absolute bound on this exact echo is a DERIVED RH criterion, not an established estimate. Actual first-product windows have both signs despite nonnegative $\Lambda*\Lambda$. The certified visible critical-zero input also rules out eventual constant one-sided bounds on $S$; even the RH case permits linear oscillation.

Native physical/projection adapters, full boundary summation, source Hermite formulas and common real-input synthesis were paid rather than assumed. They reveal genuine compatibility and costs. They do not make a fixed input an eigenstate, turn nonunitary index transport into an isometry, or turn generic noncollision into a uniform gap. Full normal, reciprocal and exterior-response terms survive. In several exact compositions the retained boundary derivative returns the original echo with coefficient one. Repeating that identity is not an opposing arithmetic estimate.

**Reading order for Pro or the next researcher.** Start with the published `HANDOVER.md` (this document), `PORTABLE_ARCHIVE_MANIFEST.json`, `CHECKPOINT.json`, and `READING_MAP.md`. The checkpoint includes the latest pointer and publication state; the manifest and reading map locate the archived research and evidence. Absolute historical paths inside old records are provenance, not portable dependency declarations. Within the archived closure research, read these groups in order:

1. `new-energy-continuation/MERTENS_COUNTING_AND_APERTURE_COMPLETION.json` (`328a3bc9`) and the latest post-resume aggregate. These distinguish current authority from the many older checkpoints.
2. `ground/fixed-k3-aperture/ACTUAL_FIXED_K3_ARITHMETIC_SCALARS.json`, `ACTUAL_FIXED_K3_APERTURE_LANDAU_DERIVATION.json`, and `ACTUAL_K3_SIGNED_EXCURSION_RATES.json`: literal normalization, complete-zero reduction, exact strength.
3. `ground/fixed-k3-aperture/arch-formal-specialization/COMPLETION.json` (`f10703b5`) and its six-root dependency inventory: the actual locally compiled Arch theorem and validation limits.
4. `arithmetic/k3-higher-prime-powers/` and `arithmetic/k3-prime-counting-compensation/`: full signed budget, Mertens-only improvement, exact remaining ordinary-prime target.
5. `ground/fixed-k3-aperture/global-aperture-seams/` (`3129e82`) and `negative-well-source-storage/` (`4e6e7899`): complete forcing, corrected coefficient, history cost and reviews.
6. `arithmetic/k3-generated-prime-energy/` (`a7a5b1d0`; peer `2b3ec90e`): full generated-square falsification and original-window distinction.
7. `new-energy-continuation/JOINT_DECONVOLUTION_SELF_ECHO_REVIEW.json`, plus `arithmetic/finite-boundary-summation/`, `common-real-source-synthesis/` and `ground-residual-compensation/`: paid older bridges and their exact surviving costs.

**Best next reasoning after the break.** Seek a genuinely independent signed arithmetic bound on the displayed $\mathcal E_{\rm ord}$, or a source-specific control of the complete negative-well storage/replenishment and signed residual. Any proposal should first be checked against the known $L^5$ compensation, both exponential prime charges, actual forcing seams, and the generated-square asymptotic. A mathematical supplier would change the state; another equivalent target, unsigned majorant, or unpriced inverse would not. Formalizing the finite Mertens square bound is useful supporting work, but must not be presented as closing the ordinary-prime gap. Do not restart the already rejected positivity, missing-history, rightmost-zero, or trial-equals-ground shortcuts.

The requested break begins after publication is verified. This handover schedules no continuation and makes no promise of closure.

## Portable publication and graph scope

The [reading map](READING_MAP.md) links byte-identical current reports. The [outcome register](OUTCOME_REGISTER.json) includes positive and negative results; the [evidence map](RESEARCH_DEPENDENCIES.json) records hash-bound references, not new theorem implications. The unchanged canonical graph producers discover the published documents; external source files remain provenance. No archived helper is an instruction to execute it.

The archive is stored in ordered byte parts, each at most 7 MiB. `python read_archive.py --verify` validates the complete archive and all indexed contents. `python read_archive.py --list` lists logical research paths; `python read_archive.py --show LOGICAL_PATH` displays a selected text file without extraction. Original Windows paths inside old receipts retain their historical meaning; the portable manifest supplies the actual locations. Compiled objects, dependency caches, raw downloads and private transport metadata are explicitly excluded; see [the exclusion inventory](EXCLUDED_ENVIRONMENT_INVENTORY.json).

The full publication head must receive its own CI qualification. Baseline7bae successes are historical evidence for that exact head. This publication preserves the 1079/90 production proof scope and the 277-method register; it does not claim Step4 closure. Research is paused after the verified push at the maintainer request.

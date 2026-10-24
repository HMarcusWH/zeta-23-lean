# OPICA follow-up — proposed Post-Green mathematical amendment v1.1

**Date:** 2026-10-21  
**Audience:** builder/auditor of the proposed OPICA follow-up to `HMarcusWH/zeta-23-lean` PR #293  
**Status:** **AMENDMENT PROPOSAL / DERIVED MATHEMATICS / NOT YET LEAN PROVED**  
**Relationship to normative build:** supplemental to `OPICA_FOLLOWUP_PR_BUILD_SPEC_2026-10-21.md`, `OPICA_FOLLOWUP_BUILD_MANIFEST_2026-10-21.json`, `OPICA_FOLLOWUP_PUBLIC_ROOTS_2026-10-21.json`, the source PDFs and their frozen paper counterparts. **Do not overwrite or silently reinterpret those sources.**

## A. Scope, baseline and claim firewall

1. **The target is the NEW sibling follow-up PR, not an amendment to the already-merged parent PR #293.** The specification's `OPEN_DRAFT_NOT_MERGED`, `parent_draft=true`, `parent_merged=false`, and pending parent acceptance records reflect an earlier observation. Before implementation, check live GitHub, identify the exact accepted merge commit/tree and current main; reconcile its source/API with the pinned PR head `553b4263b58d9fec178320de251ff299a0bd702a` and tree `12691099f1a155a8bfa3ad4f6689146175b233b2`. Verify compiler receipts and all workflow/research dispositions; do not mark jobs green based on a successful workflow wrapper alone. If accepted tree is unchanged, record that source equivalence explicitly; if changed, rebase and version the provenance.
2. The normative follow-up currently has **100 primary roots / 28 acceptance units / 43 Lean files / 84 new paths / 12 existing authoritative edits**, plus the stated generated outputs. **Preserve these counts and definitions by default.** These additions should initially be **nonblocking candidate lemmas** in already-planned modules, not covertly added acceptance gates. If promoted to mandatory roots, publish v1.2 manifests, type consumers, crosswalk, parent-extension ID/path policy, contracts and regenerated validations with exact new counts. Do not append a root ID to a frozen ledger without its own reviewed statement and proof.
3. These claims are **DERIVED (paper-level)**. New Lean declarations are **PROVED** only after exact current-tree compilation, verified types/assumptions, approved axioms and no-sorry audit. None by itself closes RH, Step 4, A-X, B-Y, C-Schur, OPEN-J46, or the independent signed high-mask / boundary-amplitude obligations.

## B. Candidate 1 — sharp norm-first transfer in seminormed additive groups

**Suggested module:** `Zeta23/OPICAFollowup/NormFirstTransfer.lean` (already in scope).  
**Keep the existing root** `norm_first_log_comparison` and its real/complex Hilbert-space statement as written. Prove a stronger helper first; specialize it to recover the root without changing the expected type.

For `u,v` in a seminormed additive group, set `d=‖u-v‖` and `α(d)=(d+√(d²+4))/2`. Then

\[
\left|\log(1+\|u\|^2)-\log(1+\|v\|^2)\right|
\le 2\log\alpha(d)=2\operatorname{arsinh}(d/2)
\le2\log(1+d).
\]

Proof reduction: `α>0`, `α-α^{-1}=d`, and for every `b≥0`,

\[
\alpha^2(1+b^2)-(1+(b+d)^2)=\alpha d(b-\alpha^{-1})^2\ge0.
\]

Apply `|‖u‖-‖v‖|≤d` and reverse directions. The constant is optimal: in `ℝ`, take `u=α(d)`, `v=α(d)^{-1}`. For `F=S+B`, `Q=‖B‖²-L` with real `L`, append the already required positive-part comparison:

\[
\left|\log(1+\|F\|^2)-\log(1+[Q]_+)\right|
\le2\operatorname{arsinh}(\|S\|/2)+\log(1+|L|).
\]

**Falsification checks:** `d=0`, a non-Hausdorff seminorm (nonzero seminorm-null vectors), `B=0`, `Q<0`, scalar equality, and no accidental assumption that squared-energy error is small. The native `L²` identification remains in a native consumer.

## C. Candidate 2 — polynomial-growth signed sharp-gap classification

**Suggested home:** an internal supporting theorem in `Zeta23/OPICAFollowup/NearGapLimits.lean` importing P0 `SignedHeatSeparator`; if this requires a new module, amend the path inventory **before** creating one. Do not modify the parent P0 proof.

Let `ν` be a **real signed Radon measure** whose total variation has some polynomial growth: for `R≥0`, `|ν|([-R,R]) ≤ C(1+R)^N`. Regard `ν` as a tempered distribution, with the heat Fourier convention `exp(-2πixξ)`. Assume (i) `ν̂=ν` as tempered distributions, (ii) `ν|_{(-1,1)\setminus\{0\}}=0` as an exact measure restriction, and (iii) the restriction of `ν` to `ℝ\setminusℤ` is nonnegative. Then

\[
\boxed{\nu=\nu(\{0\})\sum_{n\in\mathbb Z}\delta_n.}
\]

The origin-zero case implies `ν=0`. Evenness follows from exact Fourier self-duality (`\widehat{\widehatν}=ν(-\cdot)`), so should not be needlessly assumed independently.

**Proof design.** Let `Δ(x)=(1-|x|)_+`, `s(x)=(sin πx/(πx))²`, with `Δ̂=s`. Pick a real even nonnegative `C∞` compactly supported approximate-identity `φ_ε`, mass one, and `ψ_ε=φ_ε*\widetilde φ_ε`. Set `f_ε=Δ*ψ_ε`, so `\widehat f_ε=s|\widehat φ_ε|²≥0`. `f_ε` has uniformly bounded compact support, while `\widehat f_ε` is Schwartz; the distribution Fourier pairing is therefore legitimate for polynomial-growth `ν`. Fourier self-duality gives

\[
\int_{\mathbb R\setminus\mathbb Z}s|\widehat φ_ε|²\,dν
=\int f_ε\,dν-ν(\{0\})\longrightarrow0.
\]

The convergence follows from uniform `f_ε→Δ` on a **fixed compact set** and the exact unit gap. The left integrand is nonnegative against the **positive off-lattice measure**. Fatou yields `∫_{ℝ\setminusℤ}s dν=0`; `s>0` there, so the measure is supported on `ℤ`. A lattice-supported Fourier-self-dual measure is 1-periodic (its Fourier transform has integer support), hence all lattice weights are equal. This establishes the result.

**Boundaries:** polynomial growth is NOT the same as order-zero positivity for a generic tempered distribution; no classification is claimed for distributions containing derivatives of atoms. Do not promote this helper as a new native construction of a self-dual, positive sharp-gap measure.

## D. Candidate 3 — finite-stage four-cost approximate separator

**Suggested home:** `NearGapLimits.lean` and, for the actual arithmetic interface, `Consumers.lean` as a **conditional consumer only**.

With the same compact regularizer set `w_ε=s|\widehat φ_ε|²` and define, for an arbitrary polynomial-growth real signed measure,

\[
P_ε=\int_{\mathbb R\setminus\mathbb Z}w_ε\,dν_+,\qquad
N_ε=\int_{\mathbb R\setminus\mathbb Z}w_ε\,dν_-,\qquad
D_ε=\langle\widehatν-ν,f_ε\rangle.
\]

Retain the **exact tested identity**

\[
P_ε-N_ε=D_ε+\int f_ε\,dν-ν(\{0\}).
\]

If `0<a≤1` and `ν|_{(-a,a)\setminus\{0\}}=0`, and the autocorrelation kernel is supported within `[-ε,ε]`, then

\[
P_ε\le N_ε+|D_ε|+(1-a)|ν|([-1,1])+ε|ν|([-2,2]).
\]

For `R≥1`, `0<d≤1/2`, `E_{R,d}={|x|≤R,dist(x,ℤ)≥d}`, and `ε≤(2πR)^{-1}`, one obtains

\[
\boxed{\frac{d^2}{\pi^2R^2}\,ν_+(E_{R,d})
\le N_ε+|D_ε|+(1-a)|ν|([-1,1])+ε|ν|([-2,2]).}
\]

This prices, respectively, **negative observation mass, tested Fourier duality defect, gap deficit, and smoothing/local-variation cost**. It is usable without convergence to an exactly self-dual limiting measure, but still demands a genuine order-zero measure and valid absolute pairings.

**Native rate consumer, only if separately proved:** if the actual source energy satisfies `E_T≤b_T P_{ε_T}+c_T` and all four right-hand costs, including factors `b_T,c_T` and observation penalty `R_T²/d_T²`, are `exp(o(T))`, then `E_T=exp(o(T))`. Combined with a separately proved native J5.2, this would imply `Θ=0`. **No such native source-to-measure bound has been proved or is authorized as an assumption-free root.** Record the missing map/defect bounds as OPEN, not as hidden fields on a `NativeCandidate` structure.

**Falsification controls:** (a) nonzero integer comb, which is allowed when origin mass is nonzero; (b) gapped off-lattice positive atoms with a large `D_ε`; (c) sign-changing off-lattice cancellation; (d) ε→0 while derivative/duality costs diverge; (e) a positive witness approaching the integer lattice so `d→0`; (f) witnesses escaping with `R→∞`; (g) normalized dilation distributions containing `δ'` or `δ''`, which cannot be fed to the measure theorem.

## E. Candidate 4 — short lattice-repair obstruction

**Suggested module:** `SquareDefect.lean` as a separate auxiliary lemma. A lattice-supported polynomial-growth measure `η` satisfies `∫w_ε dη=η({0})`, while `∫f_ε dη→η({0})`. Hence no such measure correction can cancel the self-duality defect of a nonzero positive off-lattice gapped component while preserving the stated hypotheses. **Retain** the paper's exact square-family convolution defect identity, the origin calculation, and the self-dual-projection gap-filling countercontrol; this is a shorter supporting argument, **not** a replacement for the required R2-S3 roots. Distributional lattice corrections involving delta derivatives require separate analysis.

## F. Acceptance and next research decision

- **Before coding:** refresh `PARENT_INTAKE`, exact source/check hashes and actual workflow harvest against the accepted PR #293 tree. Do not silently rewrite frozen sources or their SHA-256 fields.
- **During coding:** implement required original 100 roots first; add the above as separately named **optional** helpers if they reduce proof burden, without changing existing mandatory expected types. If an extension is made mandatory, issue a fully versioned manifest/crosswalk/root/receipt amendment and update counts; never describe a partial slice as a complete green follow-up.
- **During review:** distinguish Lean-proof facts, derived but not yet Lean formal results, numerical regression results and OPEN conditional consumers. Inspect exact assumptions and non-vacuity. Do not interpret a green replay as a new RH theorem.
- **After any green:** inspect full workflows, actual proofs and dependency delta. Attempt falsification of the native four-cost bound on the physical `j` / `Pj` source, not a chosen toy comb. The high-leverage question is whether `D_ε` has a **genuinely independent bound** or merely repackages the original high-mask energy.

**Research status:** the exact follow-up package remains a supporting formalization program. RH and Step 4 remain OPEN.

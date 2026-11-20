# Pass20: positive source Grams and the exact terminal collar

9 November 2026. **DERIVED paper analysis**, using the actual original compact source, full ordinary prime-power measure, and ordinary PNT. No new Lean theorem, repository mutation, source substitution, numerical experiment, or CI run. Formal reference head: b3afa611d3181f38c2d3c8a69c64d318ee2ea6d7. Step 4 and RH remain OPEN.

The source really is positive definite. Its factorization yields a valid energy inequality. However, applying that inequality to the exact finite arithmetic cutoff produces a positive Gram whose leading exponential mass lies in the required terminal collar, outside the observed prefix. The full divisor-completed pairing of that truncated source also has an explicitly positive exponential terminal term. The bounded completion pairing for the *untruncated genuine field* cannot be substituted for it.

This is an actual-prime calculation. It does not replace the prime measure by a free positive measure, and it does not infer a sign for the complete prefix covariance from positivity of its Gram.

## 1. What positive definiteness actually pays

Keep \(s_0=1/4096\), \(S=2s_0=1/2048\), and the fixed real even nonnegative smooth q with support in \([-s_0,s_0]\) and integral one. Put
\[
\kappa=(D^2-\tfrac14)q,\qquad h=\kappa*\kappa.
\]
Thus \(\kappa\) and h are real even, with supports respectively \([-s_0,s_0]\) and \([-S,S]\). For the Fourier convention \(\widehat f(\xi)=\int e^{-i\xi t}f(t)\,dt\),
\[
\widehat h(\xi)=H(i\xi)
=(\xi^2+\tfrac14)^2Q(i\xi)^2=|\widehat\kappa(\xi)|^2\ge0.
\]
For every finite real signed measure \(\nu\),
\[
G_h(\nu):=\iint h(u-v)\,d\nu(u)d\nu(v)
=\|\kappa*\nu\|_2^2\ge0.
\]
This identity does not require the coefficients of \(\nu\) to be positive. Let
\[
M_h=\sup_{\xi\in\mathbb R}H(i\xi)<\infty.
\]
Plancherel gives the genuine upper
\[
\boxed{\ \|h*\nu\|_2^2\le M_h G_h(\nu).\ }               \tag{1}
\]
Indeed \(H(i\xi)^2\le M_h H(i\xi)\) pointwise. All cross terms remain. There is no global reverse coercivity obtained this way: the Fourier multiplier tends to zero at infinity.

The question is therefore whether the *actual* finite prime input has an independently small \(G_h\), not whether this Gram is nonnegative. The calculation below answers the first, overly strong, version negatively.

## 2. Preserve the original raw cutoff for the observed prefix

Write
\[
\Pi=\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}\delta_{\log n},
\qquad P=\Pi*h.
\]
All proper prime powers are included. For an observation horizon H define
\[
L=H+S,\qquad
\mu_H=\sum_{2\le n\le\lfloor e^{H+S}\rfloor}
\frac{\Lambda(n)}{\sqrt n}\delta_{\log n},
\qquad P_H=h*\mu_H.
\]
This is exactly the original raw cutoff, not the different outer inverse or Vaughan cutoff.

For \(0\le t\le H\), every omitted pulse has argument below \(-S\), so
\[
P_H(t)=P(t).
\]
The truncated field is zero after \(H+2S=L+S\), and is zero before \(\log2-S>0\). Consequently
\[
\boxed{\
\|P_H\|_{L^2(\mathbb R)}^2
=\underbrace{\int_0^H|P(t)|^2dt}_{E(H)}
+\underbrace{\int_H^{H+2S}|P_H(t)|^2dt}_{B(H)} .
\ }                                                     \tag{2}
\]
In particular the whole-line positive Gram energy cannot be substituted for \(E(H)\) without paying \(B(H)\).

## 3. A uniform actual-prime terminal profile

Here is a fixed-profile lemma, proved with all endpoints included. Let f be a nonzero smooth real function supported in \([-r,r]\), with \(r<\log2\), and suppose
\[
\int e^{-v/2}f(v)\,dv=0.
\]
Use the same prime-power cutoff at logarithmic endpoint L:
\[
F_{f,L}(t)=\sum_{n\le e^L}\frac{\Lambda(n)}{\sqrt n}f(t-\log n).
\]
Let \(\psi(x)=\sum_{n\le x}\Lambda(n)\). Ordinary PNT gives \(\psi(x)/x\to1\): it follows from \(\pi(x)\sim x/\log x\) by partial summation, with the proper-power difference bounded by \(O(\sqrt{x}\log^2x)\). Only this qualitative, unconditional theorem is used; no shrinking interval or RH error estimate occurs. [NIST DLMF, ordinary PNT](https://dlmf.nist.gov/27.2.E3).

For \(v\in[-r,r]\), put
\[
b_f(v)=e^{v/2}\int_v^r e^{-w/2}f(w)\,dw.
\]
Extend \(b_f\) by zero outside that interval. The tilted moment makes it smooth at the left endpoint; smooth support handles the right endpoint. The complete statement is
\[
\boxed{\ e^{-L/2}F_{f,L}(L+v)\longrightarrow b_f(v)
\quad\hbox{uniformly for }v\in[-r,r].\ }                 \tag{3}
\]

To check uniformity and the upper cutoff, set
\[
A_L(x)=e^{-L}\psi(e^Lx),\quad a=e^{-2r},\quad
\phi_v(x)=x^{-1/2}f(v-\log x).
\]
The exact normalized Stieltjes integral is \(\int_a^1\phi_v\,dA_L\). The test is zero at a, while its generally nonzero value at 1 is retained. For
\[
\varepsilon_L=\sup_{y\ge e^{L-2r}}|\psi(y)/y-1|\longrightarrow0
\]
integration by parts gives
\[
\left|\int_a^1\phi_v\,d(A_L-x)\right|
\le\varepsilon_L
\left[\|f\|_\infty+
2(e^r-1)(\|f'\|_\infty+\tfrac12\|f\|_\infty)\right].     \tag{4}
\]
The continuous main \(\int_a^1\phi_v(x)dx\) is exactly \(b_f(v)\). Formula (4) includes a possible prime-power atom at the actual upper cutoff; it is not a strict-endpoint approximation.

The unrestricted field \(F_f=\Pi*f\) also satisfies
\[
F_f(t)=o(e^{t/2})
\]
by the same Stieltjes calculation on the full fixed multiplicative support and the tilted moment. Therefore
\[
\int_0^{L-r}|F_f(t)|^2dt=o(e^L).
\]
For completeness, choose a fixed late T with \(|F_f(t)|\le\varepsilon e^{t/2}\) for every \(t\ge T\), integrate, divide by \(e^L\), and then let \(\varepsilon\downarrow0\). No uniform-in-hypothetical-zero estimate is being used.

Since \(F_{f,L}=F_f\) before \(L-r\), while the whole output ends at \(L+r\), (3) proves
\[
\boxed{\ \|F_{f,L}\|_2^2
=e^L\bigl(\|b_f\|_2^2+o(1)\bigr).\ }                    \tag{5}
\]
The constant is strictly positive: \(b_f'-b_f/2=-f\), so \(b_f=0\) would force \(f=0\).

## 4. The terminal constants are explicit for the actual source

Apply the lemma first to \(\kappa\), with \(r=s_0\), and then to h, with \(r=S\). Both tilted moments vanish because their transforms have the required zero at \(1/2\).

For \(\kappa\), compact integration gives
\[
b_\kappa(v)=-q'(v)-\tfrac12q(v),
\]
and hence
\[
c_\kappa:=\|b_\kappa\|_2^2
=\|q'\|_2^2+\tfrac14\|q\|_2^2>0.                        \tag{6}
\]
The cross derivative integrates to zero by compact support.

For h,
\[
b_h(v)=e^{v/2}\int_v^S e^{-w/2}h(w)\,dw,\qquad
b_h'-b_h/2=-h.
\]
Thus
\[
D_h:=\|b_h\|_2^2
=\frac1{2\pi}\int_{\mathbb R}
\frac{|H(i\xi)|^2}{\xi^2+1/4}\,d\xi>0.                  \tag{7}
\]
This is exactly the source constant already encountered in the Pass18 complete-pulse cross calculation; its terminal interpretation here is new bookkeeping, not a new definition of the source.

Equations (2)–(7), with \(L=H+S\), give
\[
\boxed{
\begin{aligned}
G_h(\mu_H)&=e^{H+S}\bigl(c_\kappa+o(1)\bigr),\\
\|P_H\|_2^2&=e^{H+S}\bigl(D_h+o(1)\bigr),\\
B(H)&=e^{H+S}\bigl(D_h+o(1)\bigr),\\
E(H)&=o(e^H).
\end{aligned}}                                        \tag{8}
\]
The \(\kappa\)-Gram's leading collar is
\([H+s_0,H+3s_0]\), also entirely beyond the observed prefix.

Therefore the valid positive-factorization upper (1) gives an exponential allowance at the exact raw cutoff. A proposed polynomial bound on this *whole-line* positive Gram is false for the genuine input, unconditionally. This is not a counterexample to a polynomial or subexponential bound for \(E(H)\); the distinction is precisely (2).

## 5. The complete energy covariance and its boundary subtraction

Let \(K=h*h\), the real autocorrelation of h. Then
\[
\|P_H\|_2^2
=\sum_{m,n\le e^{H+S}}\frac{\Lambda(m)\Lambda(n)}{\sqrt{mn}}
K(\log m-\log n).
\]
The exact observed-prefix energy is thus
\[
\boxed{\ E(H)=
\sum_{m,n\le e^{H+S}}\frac{\Lambda(m)\Lambda(n)}{\sqrt{mn}}
K(\log m-\log n)-B(H).\ }                               \tag{9}
\]
Both terms on the right are nonnegative and have the same exponential main \(e^{H+S}D_h\). Their difference remains nonnegative by its original integral definition. Positivity supplies neither the accuracy of their cancellation nor a polynomial upper for the difference.

Even the diagonal is misleadingly small. Ordinary PNT and partial summation give
\[
\sum_{n\le e^L}\frac{\Lambda(n)^2}{n}=O((1+L)^2).
\]
The proper-power contribution with exponent at least two is bounded by
\(\sum_{m\ge2}(\log m)^2/[m(m-1)]<\infty\); the prime contribution is handled with the ordinary weighted prime count. Thus the entire diagonal in (9)'s Gram is polynomial, while the complete off-diagonal plus diagonal has the exponential size in (8). Positive definiteness does not justify replacing the full Gram by its diagonal.

The parent pass separately tests the proposed monotonicity under adjoining positive prime bands, using an actual negative interval of K and keeping its full band cross pairing. That is complementary to this note: no entrywise nonnegativity of K, or monotonicity of energy under positive measure addition, has been used here.

## 6. The divisor-completed pairing also retains an exponential terminal term

The completion relation cannot be applied beyond its unchanged prefix. Retain the actual
\[
T=(D+3/2)a=(I-C_-)*N,\qquad V=TP,
\]
where a is the full floor kernel and \(C_-\) has causal kernel \(e^{-t/2}\). The source-specific Pass16 bound pays
\[
\int_0^\infty|P(t)V(t)|dt<\infty.
\]
It does not assert \(TP_H=V\) after H.

To compute the missing part, let \(F_H=P-P_H\). This is exactly the omitted prime-power source field, and it is zero up to H. For \(H\le t\le H+2S\), the inequality \(2S<\log2\) means that no nontrivial integer delay can yet act on \(F_H\). Consequently
\[
TF_H=(I-C_-)F_H
\]
on that entire collar. This keeps all original integer histories: it uses their actual positive first-delay threshold, not a substituted kernel.

Write \(t=L+v\), \(v\in[-S,S]\). Equations (3) and (8) give uniformly
\[
e^{-L/2}P_H(L+v)\to b_h(v),\qquad
e^{-L/2}P(L+v)\to0,\qquad
e^{-L/2}F_H(L+v)\to-b_h(v).
\]
The completed full field V is rapidly decaying. Therefore the exact identity \(TP_H=V-TF_H\) implies
\[
e^{-L/2}TP_H(L+v)\to
b_h(v)-\int_{-S}^v e^{-(v-u)/2}b_h(u)\,du.              \tag{10}
\]
Finite-interval convolution preserves the uniform convergence, so no limit of an uncontrolled infinite history is taken.

Because \(P_H\) is zero after \(H+2S\), its full completed pairing is exactly the bounded prefix pairing plus the collar. Hence
\[
\boxed{\
\int_{\mathbb R}P_H(t)TP_H(t)\,dt
=e^{H+S}\bigl(\beta_h+o(1)\bigr),\quad
\beta_h=\int_{-S}^S b_h(v)(I-C_-)b_h(v)\,dv .
\ }                                                     \tag{11}
\]
On this interval the causal convolution has norm at most
\(2(1-e^{-S})\le2S\). Thus
\[
\boxed{\ \beta_h\ge(1-2S)D_h>0.\ }                      \tag{12}
\]
The constant is fixed by the unchanged source before H.

This is a concrete full-source falsification of the tempting substitution
\(\langle P_H,TP_H\rangle=\langle P,TP\rangle_{[0,H]}\).
The first grows exponentially by (11); the second is uniformly bounded by the paid genuine-source relation. Every part of that difference is in the explicit terminal collar. No hypothetical off-line zero or generic positive-measure countermodel is needed.

## 7. What remains after the falsification

The useful positive factorization is (1), and the literal finite cutoff has now been accounted for exactly. Neither removes the signed estimate still required by the closing theorem:

- Keeping the whole positive Gram gives the exponential term in (8).
- Removing that term through the exact collar returns the difference (9), whose required cancellation accuracy remains unproved.
- Using the bounded full-source completion without the collar makes the false substitution contradicted by (11).
- Discarding signed cross terms is not licensed by Fourier positivity.

Ordinary effective PNT can quantify the little-oh remainders, but its familiar fixed-source energy allowance still has leading exponent one with a smaller stretched-exponential correction. It is not an upper for every requested positive exponent. No stronger PNT error is assumed here.

Historical work already established exponentially large *selected prime-block* completion quadratics and balanced-semiprime energy components, with complete compensating complements retained. This note does not claim that those phenomena are new. Its narrower calculation uses the entire actual initial prime-power measure at the exact original cutoff \(\lfloor e^{H+S}\rfloor\), proves where its positive Gram mass lives, identifies the same \(D_h\) constant, and pays the derivative-completion collar explicitly.

No independent prefix-energy upper, native whole-carrier PG/SB floor, or Step 4 supplier has been obtained. The genuine arithmetic covariance after the exact boundary correction remains OPEN.

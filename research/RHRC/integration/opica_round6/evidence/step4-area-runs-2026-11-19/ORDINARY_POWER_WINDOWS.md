# Opposite signs of the ordinary-prime area in every late power interval

**DERIVED on paper.** Write \(B=\sup_\rho\Re\rho\). If \(B>1/2\), then for every fixed \(\eta>0\) and any actual zero real part \(b>1/2\) sufficiently close to \(B\), every sufficiently late interval \([X,X^{1+\eta}]\) contains two points \(y_+,y_-\) with
\[
 A_\pi(y_+)>\kappa\,y_+^{1+b}/\log y_+,\qquad
 A_\pi(y_-)<-\kappa\,y_-^{1+b}/\log y_-
\]
for some \(\kappa>0\) fixed before \(X\). One may take any \(b>B/(1+\eta/2)\) with \(b>1/2\). This treats an unattained supremum. If a zero attains \(B>1/2\), the [direct boundary-frequency series](DENSITY_ISOLATOR.md) already establishes both signs on the smaller multiplicative scale. Under RH, Johnston proves \(A_\pi(x)<0\) for all \(x>2\). [Johnston, Theorem 1.1](https://arxiv.org/pdf/2201.06184#page=1)

## Retaining the earlier prime history

Put \(t_0=\log2\), \(P(t)=A_\pi(e^t)\), \(V(t)=A_\vartheta(e^t)\), \(p=1+b\), and \(L=D^2-D\). As distributions on \(t>t_0\), one has the exact identity \(LV=tLP\). Indeed, on the physical variable \(x\), \(A_\vartheta''=d\vartheta/dx-1=\log(x) A_\pi''\), including the jumps, by the definitions of \(\vartheta,\pi,\operatorname{li}\). The log substitution contributes the same \(e^{2t}\) to both sides. Consequently, with two finite constants fixed by the initial data,
\[
 tP(t)-V(t)=c_0+c_1e^t+
  \int_{t_0}^t(1+e^{t-v})P(v)\,dv.                              \tag{1}
\]
For example \(L(tP-V)=2P'-P\); applying \(L\) to the displayed integral gives exactly \(2P'-P\). This accounts for all history before the observation window.

Use the [positive zero-isolating measure](DENSITY_ISOLATOR.md) on \([0,W]\) for \(b\). Its integral \(I(t)=\int V(t+u)d\nu(u)\) satisfies \(|I(t)|\le C e^{pt}\), and on each interval of some fixed length at sufficiently late times it has both an upper excursion \(I(t)>a e^{pt}\) and a lower excursion \(I(t)<-a e^{pt}\), with \(a>0\). Write
\[
 F(t)=\int P(t+u)d\nu(u),\qquad G(t)=\int uP(t+u)d\nu(u).
\]
Applying the measure to (1) yields
\[
 tF+G=I+Q_0+Q_1,\qquad Q'_0=F,\qquad Q'_1=Q_1+F.               \tag{2}
\]
The parts of the two integrals between \(t_0\) and \(t_0+u\), after shifting the integration variable, contribute a constant and a multiple of \(e^t\), respectively. Both are retained in the initial data of \(Q_0,Q_1\). The same system holds on changing the signs of all its variables simultaneously. From \(|A_\vartheta(x)|\ll x^{1+B}\) and [ordinary-prime partial summation](../step4-strip-2026-11-19/ORDINARY_PRIME_AREA.md), \(|P(t)|\ll e^{(1+B)t}\). The two evolution equations therefore give
\[
 |Q_0(T)|+|Q_1(T)|\ll_\nu e^{(1+B)T}.
\]

## A one-sided comparison deep within the window

Take a sign \(s\in\{1,-1\}\), replacing the entire system by its multiple \(s\). Suppose throughout \([T,(1+\eta)T]\) that the resulting ordinary field satisfies \(P(v)\ge-\kappa e^{pv}/v\), with \(0<\kappa\le1\) to be fixed. On \(T\le t\le(1+\eta)T-W\), positivity of the averaging measure implies
\[
 F(t)\ge-\kappa e^{pW}e^{pt}/t,\qquad
 G(t)\ge-\kappa W e^{pW}e^{pt}/t .
\]
By (2), for \(T\ge1\) it follows that \(|F(t)|\le(C' e^{pt}+H(t))/t\), where \(H(t)=|Q_0(t)|+|Q_1(t)|\) and \(C'\) can be chosen independently of \(\kappa\le1\). Solving the two first-order equations gives
\[
 e^{-t}H(t)\le e^{-T}H(T)+
  2\int_T^t\frac{C'e^{bv}+e^{-v}H(v)}{v}\,dv.
\]
Gronwall's inequality has factor at most \((t/T)^2\le(1+\eta)^2\) here. Using \(\int_T^t e^{bv}/v\,dv\le e^{bt}/(bT)\) gives
\[
 H(t)\ll_{\eta,\nu} e^{t+BT}+e^{pt}/T.
\]
If \((1+\eta/2)T\le t\le(1+\eta)T-W\), the choice \(b(1+\eta/2)>B\) makes \(H(t)=o(e^{pt})\) uniformly. For sufficiently large \(T\), this last interval contains a negative excursion of \(I\) of depth \(a e^{pt}\) for either choice of the overall sign. At that point \(tF+G\le-(a/2)e^{pt}\), contradicting the two lower bounds once \(\kappa e^{pW}(1+W)<a/2\). This proves the asserted opposite excursions.

The incoming history \(e^{t+BT}\) explains the spacing in the conclusion. When \(b<B\), a bounded log-time distance does not make this term smaller than \(e^{(1+b)t}\). The argument supplies no constant multiplicative spacing for \(A_\pi\) in that case. Its power-window result still leaves open the independent arithmetic sign estimate required for Step 4.

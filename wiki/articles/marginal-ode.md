---
{
  "id": "marginal-ode",
  "title": "A marginal ODE and its logarithmic correction",
  "subtitle": "An integrating-factor argument with an explicit error condition",
  "kind": "method",
  "category": "Methods",
  "summary": "A nonlinear correction to power-law growth produces a logarithmic factor. An integrable multiplicative error preserves the leading constant, while an error of order 1/log r can introduce another logarithm.",
  "context": ["The nonlinear marginal results use positive constants $a,\\gamma,C$ and a positive continuously differentiable function $g$ on $[r_0,\\infty)$, with $r_0>1$; the signed linear result states its own hypotheses.", "The perturbations below are continuous; the error in the nonlinear coefficient tends to zero.", "This is an analytic statement. Applying it to percolation requires a separately justified differential equation."],
  "related": ["cutoff-families", "susceptibility", "triangle-condition"],
  "sourceIds": ["notes", "hutchcroft-lrp-1"],
  "aliases": ["marginal ODE", "logarithmic correction", "integrating factor", "Bernoulli equation", "critical dimension"],
  "prototypeUses": []
}
---

## A signed linear equation with regularly varying forcing {#section-signed-forcing}

<a id="tag-2KB9" data-assertion="theorem" data-title="Regularly varying forcing determines a signed linear asymptotic"></a>
<p>Let $a,b,A\in\mathbb R$ with $b&gt;a$. Let $h$ be a positive measurable, locally integrable function on $[r_0,\infty)$, regularly varying with index $b$. Suppose $f$ is locally absolutely continuous and, almost everywhere,</p>
<div class="math-display">$$rf'(r)=(a+\varepsilon(r))f(r)+(A+\delta(r))h(r),$$</div>
<p>where $\varepsilon,\delta$ are locally bounded measurable functions tending to zero. Then</p>
<div class="math-display">$$\frac{f(r)}{h(r)}\longrightarrow\frac{A}{b-a}.$$</div>
<p>No sign condition on $f$ or $A$, and no prior bound $|f|=O(h)$, is needed.</p>
<p><em>Proof.</em> Define $H(r)=\exp\{\int_{r_0}^r(a+\varepsilon(t))\,dt/t\}$. For each fixed $\lambda&gt;0$, the integral of $\varepsilon(t)/t$ between $r$ and $\lambda r$ tends to zero, so $H$ is regularly varying with index $a$. Variation of constants gives</p>
<div class="math-display">$$f(r)=H(r)\left[f(r_0)+\int_{r_0}^r\frac{(A+\delta(t))h(t)}{tH(t)}\,dt\right].$$</div>
<p>Put $q=h/H$. Its index is $b-a&gt;0$, and hence</p>
<div class="math-display">$$\int_{r_0}^r\frac{q(t)}t\,dt\sim\frac{q(r)}{b-a}.$$</div>
<p>One may see this directly by setting $t=ru$: on compact subintervals of $(0,1]$ the normalized integrand tends to $u^{b-a-1}$. A regular-variation bound by $Cu^{b-a-1-\eta}$, with $0&lt;\eta&lt;b-a$, controls the part where $ru$ is large; the remaining fixed initial interval contributes $o(q(r))$. Integration gives the displayed equivalent.</p>
<p>The integral containing $\delta$ is $o(q(r))$: after a fixed large threshold its absolute value is bounded by $\sup_{t\geq T}|\delta(t)|$ times the positive integral just estimated, and the initial interval is negligible. Also $H(r)/h(r)=1/q(r)\to0$. Divide the variation-of-constants formula by $h(r)$ to obtain the claim, including when $A=0$.</p>
<p>This gives the signed ODE step used for spatial monomials in <a href="https://arxiv.org/html/2508.18807v1">Critical LRP I</a>, Lemma I.5.26, with local absolute continuity sufficient. It does not differentiate a slowly varying normalization, and it does not require the error multiplying $f$ to be integrable: the positive index gap $b-a$ makes the forcing dominant. The marginal equation below has no such positive gap and requires different error control.</p>

## The asymptotic {#section-asymptotic}

<a id="tag-09N5" data-assertion="theorem" data-title="Marginal ODE asymptotic with integrable multiplicative error"></a><p>Let $a,\gamma,C&gt;0$, $r_0&gt;1$, and let $g:[r_0,\infty)\to(0,\infty)$ be continuously differentiable. Suppose continuous functions $\varepsilon,\delta$ satisfy $\varepsilon(r)\to0$ and</p><div class="math-display">$$\int_{r_0}^\infty\frac{|\delta(r)|}{r}\,dr&lt;\infty,$$</div><p>and that</p><div class="math-display">$$g'(r)=\frac ar\left[1-(C+\varepsilon(r))(r^{-a}g(r))^\gamma+\delta(r)\right]g(r).$$</div><p>Then</p><div class="math-display">$$g(r)\sim r^a(a\gamma C\log r)^{-1/\gamma}\qquad(r\to\infty).$$</div><p><em>Proof.</em> Put $t=\log r$, $t_0=\log r_0$, and $u(t)=e^{-at}g(e^t)$. Removing the leading power gives</p><div class="math-display">$$\frac{u'(t)}{u(t)}=-a(C+\varepsilon(e^t))u(t)^\gamma+a\delta(e^t).$$</div><p>Since $u&gt;0$, set $w=u^{-\gamma}$. The equation becomes linear:</p><div class="math-display">$$w'(t)+a\gamma\delta(e^t)w(t)=a\gamma(C+\varepsilon(e^t)).$$</div><p>Its integrating factor</p><div class="math-display">$$H(t)=\exp\!\left(a\gamma\int_{t_0}^t\delta(e^s)\,ds\right)$$</div><p>has a finite positive limit $H_\infty$, by the absolute integrability assumption. Consequently</p><div class="math-display">$$w(t)=\frac{w(t_0)+a\gamma\int_{t_0}^tH(s)(C+\varepsilon(e^s))\,ds}{H(t)}.$$</div><p>The integrand tends to $H_\infty C$, so its average over $[t_0,t]$ tends to the same limit. Dividing by $t$ gives $w(t)/t\to a\gamma C$. Taking the negative $1/\gamma$ power and returning to $r=e^t$ proves the assertion.</p><p>The positive limit of the integrating factor cancels from the leading coefficient. No rate of convergence or integrability is required of $\varepsilon$: it appears as a vanishing error in the forcing term of the linear equation. The error $\delta$ multiplies $w$, so it is controlled differently.</p>

## Cancellation in the moment ratio {#section-ratio}

<a id="tag-OP8F" data-assertion="theorem" data-title="A marginal deficit gap determines the logarithmic second moment"></a>
<p>Let $\alpha,a_0,c,\nu,K&gt;0$. Let $m,f$ be positive locally absolutely continuous functions on $[r_0,\infty)$, with $r_0&gt;1$, and let $a,b$ be positive measurable functions. Suppose</p>
<div class="math-display">$$m(r)\sim cr^\alpha,\qquad a(r)\sim a_0r^{-\alpha-1},\qquad b(r)\sim\nu r^{3\alpha}.$$</div>
<p>Suppose measurable functions $e_1,e_2\in[0,1]$ satisfy, almost everywhere,</p>
<div class="math-display">$$m'=am^2(1-e_1),\qquad f'=3amf(1-e_2),$$</div>
<p>and that $e_2-e_1=(K+\varepsilon(r))f^2/(bm^3)$ almost everywhere, where $\varepsilon(r)\to0$. Then</p>
<div class="math-display">$$\frac{f(r)}{m(r)^3}\sim\left(\frac{6Ka_0c^4}{\nu}\log r\right)^{-1/2},\qquad f(r)\sim c\sqrt{\frac{\nu}{6Ka_0}}\,\frac{r^{3\alpha}}{\sqrt{\log r}}.$$</div>
<p><em>Proof.</em> Put $v=f/m^3$. The two exact equations give</p>
<div class="math-display">$$(\log v)'=3am(e_1-e_2).$$</div>
<p>Thus $w=v^{-2}$ is locally absolutely continuous and satisfies</p>
<div class="math-display">$$w'=6am(e_2-e_1)v^{-2}=6(K+\varepsilon)\frac{am^4}{b}\sim\frac{6Ka_0c^4}{\nu r}\quad\text{a.e.}$$</div>
<p>Integrate after bounding the last coefficient above and below by $1\pm\eta$ times its limit, beyond a radius depending on $\eta$. This gives $w(r)/\log r\to6Ka_0c^4/\nu$. Take the inverse square root and substitute $m(r)\sim cr^\alpha$.</p>
<p>The common first-moment contribution cancels before any asymptotic expansion. In particular, the theorem needs neither a second-order equivalent for $m/(cr^\alpha)-1$ nor an integrability bound on that error. It does require the asymptotic <em>difference</em> of the deficits; an upper bound on each deficit is insufficient.</p>
<p>The analytic assumptions have an explicit witness when $a_0=\alpha/c$. Take $m=cr^\alpha$, $a=(\alpha/c)r^{-\alpha-1}$, $b=\nu r^{3\alpha}$, and</p>
<div class="math-display">$$v(r)=\left[D+\frac{6K\alpha c^3}{\nu}\log\frac r{r_0}\right]^{-1/2},\qquad f=m^3v,\qquad e_1=0,\qquad e_2=\frac{Kc^3}{\nu}v^2,$$</div>
<p>where $D\geq Kc^3/\nu$. Then $0\leq e_2\leq1$ and both equations hold. This is a witness for the scalar system, not a percolation realization.</p>
<p>In the notation of S031, if $e_1\sim I_3R$ and $e_2\sim(I_3+2I_4)R$ with $I_3,I_4&gt;0$ and $R=f^2/(bm^3)$, then their difference has $K=2I_4$. The common $I_3$ term cancels. When $a_0c=\alpha$, the second-moment coefficient is $\sqrt{\nu c^3/(12\alpha I_4)}$. The spatial estimates producing $I_3,I_4$ remain inputs; the result proves their analytic consequence only.</p>

## The power-log cutoff scale and the full tail {#section-tail}

<a id="tag-QKHV" data-assertion="corollary" data-title="Power-log cutoff scales give the normalized full volume tail"></a>
<p>Suppose the hypotheses of the <a href="/tag/9PSJ/">cutoff-to-full asymptotic transfer theorem</a> hold with $a=2$, size-biased limit the square of a standard normal variable, and scale</p>
<div class="math-display">$$s(r)=r^{2\alpha}(\log r)^{-\sigma},\qquad \alpha&gt;0,\quad\sigma\in\mathbb R,$$</div>
<p>restricted to a sufficiently large interval where it is strictly increasing. In particular, the cutoff mean and second-to-first moment ratio satisfy $m_r\sim A_1r^\alpha$ and $b_r\sim A_2s(r)$, with $A_1,A_2&gt;0$, and the multiplicative ghost comparison in that theorem is assumed. Then</p>
<div class="math-display">$$\mathbb P(T&gt;t)\sim A_1\sqrt{\frac{2}{\pi A_2}}(2\alpha)^{-\sigma/2}t^{-1/2}(\log t)^{\sigma/2}.$$</div>
<p>For integer-valued $T$, the same equivalent holds with $\mathbb P(T\geq n)$.</p>
<p><em>Proof.</em> Let $F=s^{-1}$. The equation $t=s(r)$ gives</p>
<div class="math-display">$$\log t=2\alpha\log r-\sigma\log\log r\sim2\alpha\log r,\qquad F(t)^\alpha=t^{1/2}(\log F(t))^{\sigma/2}.$$</div>
<p>Consequently $F(t)^\alpha\sim(2\alpha)^{-\sigma/2}t^{1/2}(\log t)^{\sigma/2}$. Substitute this into the transfer theorem, using its coefficient $c_*=A_1\sqrt{2/A_2}$ and $\Gamma(1/2)=\sqrt\pi$.</p>
<p>The choice $\sigma=0$ gives the high-dimensional constant in S029 when $A_1=\alpha/\beta_c$ and $A_2=A$. The choice $\sigma=1/2$ gives the marginal factor $(\log t)^{1/4}$. In the latter case the second-moment coefficient from the preceding theorem, divided by the first-moment coefficient, determines $A_2$; the factor $(2\alpha)^{-1/4}$ comes from inverting the scale and cannot be dropped. The <a href="/tag/0N85/">squared-normal moment criterion</a> supplies the required size-biased convergence when the full double-factorial moment asymptotics are available. A first and second moment equivalent alone does not supply that convergence.</p>

## Higher moments from the closed hierarchy {#section-higher-moments}

<a id="tag-5O1G" data-assertion="theorem" data-title="Double-factorial moment asymptotics from a closed power-law hierarchy"></a>
<p>Fix an integer $P\geq3$ and constants $r_0,\alpha,B,C&gt;0$. Let $m_1,\ldots,m_P$ be positive locally absolutely continuous functions on $[r_0,\infty)$, let $a$ be positive and measurable, and suppose</p>
<div class="math-display">$$m_1(r)\sim Br^\alpha,\qquad m_2(r)\sim Cr^{3\alpha},\qquad a(r)\sim\frac\alpha B r^{-\alpha-1}.$$</div>
<p>For each $3\leq p\leq P$, assume a measurable error $\varepsilon_p(r)\to0$ such that, almost everywhere,</p>
<div class="math-display">$$m_p'(r)=(1+\varepsilon_p(r))a(r)\sum_{\ell=0}^{p-1}\binom p\ell m_{\ell+1}(r)m_{p-\ell}(r).$$</div>
<p>Then, for $1\leq p\leq P$, with $(-1)!!=1$,</p>
<div class="math-display">$$m_p(r)\sim(2p-3)!!\,\left(\frac{m_2(r)}{m_1(r)}\right)^{p-1}m_1(r).$$</div>
<p>No integrability or rate of decay of the errors is required. The first two equivalents, including the finite positive second-moment amplitude $C$, are hypotheses.</p>
<p><em>Proof.</em> Put $D_p=C^{p-1}B^{2-p}$ and $A_1=A_2=1$. Suppose inductively that $m_j(r)\sim A_jD_jr^{(2j-1)\alpha}$ for $j&lt;p$. The terms containing $m_p$ have total coefficient $(p+1)(1+\varepsilon_p)a m_1$. The remaining terms use only lower moments. Since $D_jD_{p+1-j}=BD_p$, the equation becomes</p>
<div class="math-display">$$m_p'=\frac{q(r)}r m_p+D_p r^{(2p-1)\alpha-1}h(r),\qquad q(r)\longrightarrow(p+1)\alpha,\quad h(r)\longrightarrow\alpha S_p,$$</div>
<p>where</p>
<div class="math-display">$$S_p=\sum_{j=2}^{p-1}\binom p{j-1}A_jA_{p+1-j}=\sum_{j=2}^{p-1}\binom pj A_jA_{p+1-j}.$$</div>
<p>The second equality reindexes $j$ as $p+1-j$. Set $t=\log r$ and $y(t)=m_p(e^t)/(D_pe^{(2p-1)\alpha t})$. Then</p>
<div class="math-display">$$y'=-\bigl((p-2)\alpha+o(1)\bigr)y+\alpha S_p+o(1)\quad\text{a.e.}$$</div>
<p>The positive gap $g=(p-2)\alpha$ forces $y\to S_p/(p-2)$. Indeed, for each sufficiently small $\eta&gt;0$ and all sufficiently large $t$, positivity of $y$ bounds its derivative between $-(g+\eta)y+\alpha S_p-\eta$ and $-(g-\eta)y+\alpha S_p+\eta$. Multiplying these two differential inequalities by their exponential integrating factors gives</p>
<div class="math-display">$$\frac{\alpha S_p-\eta}{g+\eta}\leq\liminf y\leq\limsup y\leq\frac{\alpha S_p+\eta}{g-\eta}.$$</div>
<p>Let $\eta\downarrow0$. Thus $A_p=S_p/(p-2)$, independently of the initial value of $m_p$.</p>
<p>To solve this recurrence, let $b_n=(2n-3)!!$ for $n\geq1$. Its exponential generating series is $F(z)=\sum_{n\geq1}b_nz^n/n!=1-\sqrt{1-2z}$. The identity $FF'=F'-1$ gives</p>
<div class="math-display">$$\sum_{j=1}^p\binom pj b_jb_{p+1-j}=b_{p+1}=(2p-1)b_p.$$</div>
<p>Removing the terms $j=1,p$ leaves $(p-2)b_p$. Hence the $b_p$ obey the same recurrence and initial values as the $A_p$, completing the induction. Finally $D_pr^{(2p-1)\alpha}\sim(m_2/m_1)^{p-1}m_1$.</p>
<p>This proves the coefficient calculation in the <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L4799">notes' higher-moment induction</a>. If the hypotheses hold at every fixed order for actual moments of nonnegative random variables, <a href="/tag/0N85/">0N85</a> gives the squared-normal limit under volume bias. A finite number of moment equivalents does not give that conclusion. The <a href="/tag/XXTP/">collision estimate</a> is one route to the required closed equations, but its moment assumptions must be proved independently. The case $p=2$ has zero gap, which is why this argument cannot supply its amplitude or replace the separate marginal analysis.</p>

## Propagating a slowly varying second-moment factor {#section-slow-moments}

<a id="tag-OBTO" data-assertion="theorem" data-title="A slowly varying second-moment factor propagates through the hierarchy"></a>
<p>Retain the hypotheses of <a href="/tag/5O1G/">5O1G</a>, except replace its second-moment equivalent by</p>
<div class="math-display">$$m_2(r)\sim Cr^{3\alpha}L(r),$$</div>
<p>where $L$ is positive and continuously differentiable for sufficiently large $r$, and $rL'(r)/L(r)\to0$. Then, for every $1\leq p\leq P$,</p>
<div class="math-display">$$m_p(r)\sim(2p-3)!!\,C^{p-1}B^{2-p}r^{(2p-1)\alpha}L(r)^{p-1}\sim(2p-3)!!\left(\frac{m_2(r)}{m_1(r)}\right)^{p-1}m_1(r).$$</div>
<p>In particular, $L(r)=(\log r)^{-\sigma}$ is admissible for every real $\sigma$. The marginal value $\sigma=1/2$ gives the factor $(\log r)^{-(p-1)/2}$ in the $p$th moment.</p>
<p><em>Proof.</em> The first two cases are the assumed equivalents. At step $p\geq3$, the products in the lower-moment forcing contain the common factor $L^{p-1}$: their exponents are $(j-1)+(p-j)=p-1$. Thus, with $D_p=C^{p-1}B^{2-p}$ and $S_p$ as in the preceding proof,</p>
<div class="math-display">$$m_p'=\frac{q(r)}r m_p+D_pr^{(2p-1)\alpha-1}L(r)^{p-1}h(r),\qquad q(r)\to(p+1)\alpha,\quad h(r)\to\alpha S_p.$$</div>
<p>Normalize by setting $t=\log r$ and $y(t)=m_p(e^t)/[D_pe^{(2p-1)\alpha t}L(e^t)^{p-1}]$. Its equation is</p>
<div class="math-display">$$y'=\left[q(e^t)-(2p-1)\alpha-(p-1)\frac{e^tL'(e^t)}{L(e^t)}\right]y+h(e^t).$$</div>
<p>The coefficient tends to $-(p-2)\alpha&lt;0$. The two integrating-factor comparisons in the proof of 5O1G therefore give the same limit $A_p=S_p/(p-2)$ and the same double-factorial recurrence. This completes the induction.</p>
<p>The regularity condition implies that $L$ is slowly varying: for each fixed $c&gt;0$, integrate $L'/L=o(1/r)$ between $r$ and $cr$ to obtain $\log[L(cr)/L(r)]\to0$. Slow variation alone does not imply the derivative condition used here. For example, $L(r)=1+r^{-1}\sin(r^2)$ is positive for $r&gt;1$ and tends to one, but $rL'(r)/L(r)$ does not tend to zero. The theorem asserts a sufficient condition, not a characterization of slowly varying factors.</p>
<p>This gives the analytic propagation described in the <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L5149">notes after the marginal second-moment calculation</a>. If the closed equations and moment hypotheses hold at every fixed order for cluster volumes, <a href="/tag/0N85/">0N85</a> identifies the volume-biased limit after normalization by $m_2/m_1$. For $\sigma=1/2$ its scale is $(C/B)r^{2\alpha}/\sqrt{\log r}$. Passing to the full-cluster tail still requires the omitted-edge comparison in <a href="/tag/9PSJ/">9PSJ</a>; the resulting inversion constant is recorded in <a href="/tag/QKHV/">QKHV</a>.</p>

## An exact solution {#section-exact}

<a id="tag-SR9U" data-assertion="proposition" data-title="Exact unperturbed marginal ODE solution"></a><p>For $\varepsilon=\delta=0$ and initial value $g(r_0)=g_0&gt;0$, the unique positive solution on $[r_0,\infty)$ is</p><div class="math-display">$$g(r)=r^a\left[r_0^{a\gamma}g_0^{-\gamma}+a\gamma C\log\frac r{r_0}\right]^{-1/\gamma}.$$</div><p><em>Proof.</em> The transformed equation is $w'=a\gamma C$, with $w(t_0)=r_0^{a\gamma}g_0^{-\gamma}$. Integrating gives the formula. The bracket stays positive for $r\geq r_0$, so the solution exists on the entire stated interval. The invertible transformation and uniqueness of this linear equation also give uniqueness among positive solutions.</p><p>This formula shows directly that the initial condition affects only a lower-order additive constant in $w$. In particular, setting $\gamma=2$ gives the factor $(\log r)^{-1/2}$. Identifying $a$, $C$, or $g$ with a percolation quantity is an additional step.</p>

## A vanishing error that changes the answer {#section-error}

<a id="tag-63GS" data-assertion="proposition" data-title="A nonintegrable error produces a second logarithmic factor"></a><p>Keep $a,\gamma,C&gt;0$ and $r_0&gt;1$, set $\varepsilon=0$, and take</p><div class="math-display">$$\delta(r)=-\frac1{a\gamma\log r}.$$</div><p>For every positive initial value, the corresponding positive solution satisfies</p><div class="math-display">$$g(r)\sim r^a\bigl(a\gamma C\log r\,\log\log r\bigr)^{-1/\gamma}.$$</div><p><em>Proof.</em> With $t=\log r$ and $w=(r^{-a}g)^{-\gamma}$, the equation is $w'-w/t=a\gamma C$. Thus</p><div class="math-display">$$w(t)=t\left[\frac{w(t_0)}{t_0}+a\gamma C\log\frac t{t_0}\right].$$</div><p>The bracket is positive for $t\geq t_0&gt;0$, and $w(t)\sim a\gamma C\,t\log t$. Transforming back proves the asymptotic.</p><p>Here $\delta(r)\to0$, but $\int_{r_0}^\infty|\delta(r)|\,dr/r=\infty$. Thus merely replacing the integrability hypothesis by $\delta=o(1)$ would make the first theorem false. The example does not say that absolute integrability is necessary for every individual solution to have the first asymptotic; it shows why some additional control is needed.</p>

<p>The <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L5095">marginal ODE lemma S032 in the notes</a> is the first result above, with regularity made explicit. The notes then use a separately derived moment equation to obtain a cutoff logarithm. That application must supply the constants, the differential equation and its error bounds. Passing from a cutoff moment asymptotic to a full cluster-volume tail requires still further comparison and Tauberian input; the ODE by itself establishes none of those probabilistic steps.</p>

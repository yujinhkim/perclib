---
{
  "id": "branching-processes",
  "title": "Galton–Watson branching processes",
  "subtitle": "Extinction, total progeny and the critical generating function",
  "kind": "model",
  "category": "Models",
  "summary": "Generating functions determine extinction and expected total progeny. Critical nondegeneracy and lattice support must be kept separate when interpreting the mean-field picture.",
  "context": ["Start from one individual: $Z_0=1$.", "Each individual has an independent copy of a nonnegative integer-valued offspring variable $\\xi$, with finite mean $m$.", "The offspring law is the same in every generation."],
  "related": ["exploration", "susceptibility", "subcritical-bound", "regular-variation"],
  "sourceIds": ["notes"],
  "aliases": ["Galton–Watson", "offspring", "extinction", "total progeny", "mean field", "generating function"],
  "prototypeUses": []
}
---

## Extinction as a fixed point {#section-extinction}

<a id="tag-NCWZ" data-assertion="definition" data-title="Galton–Watson process and total progeny"></a><p>Given independent copies $\xi_{n,j}$ of $\xi$, let</p><div class="math-display">$$Z_0=1,\qquad Z_{n+1}=\sum_{j=1}^{Z_n}\xi_{n,j},\qquad T=\sum_{n=0}^{\infty}Z_n\in\mathbb N\cup\{\infty\}.$$</div><p>The empty sum is zero, so zero is absorbing. Each generation is finite almost surely. Write $\phi(s)=\mathbb E[s^\xi]$ for $0\leq s\leq1$, with $0^0=1$, and $m=\mathbb E\xi$.</p>

<a id="tag-8TFY" data-assertion="proposition" data-title="Extinction probability is the least generating-function fixed point"></a><p>The extinction probability $q=\mathbb P(\exists n:Z_n=0)$ is the least solution of $\phi(s)=s$ in $[0,1]$.</p><p><em>Proof.</em> Put $q_n=\mathbb P(Z_n=0)$. The child subtrees are independent copies of the original process, so $q_0=0$ and $q_{n+1}=\phi(q_n)$. The events $\{Z_n=0\}$ increase, giving $q_n\uparrow q$. Continuity of $\phi$ yields $q=\phi(q)$. If $r\in[0,1]$ is any fixed point, monotonicity of $\phi$ and induction give $q_n\leq r$, hence $q\leq r$.</p>

<a id="tag-BFM4" data-assertion="theorem" data-title="Extinction criterion with the deterministic critical exception"></a><p>If $m&lt;1$, extinction is almost sure. If $m=1$, extinction is almost sure unless $\xi=1$ almost surely; in that exceptional case $Z_n=1$ for every $n$ and extinction never occurs. If $m&gt;1$, survival has positive probability.</p><p><em>Proof.</em> For $0\leq s&lt;1$, the elementary inequality $s^k\geq1-k(1-s)$ gives $\phi(s)\geq1-m(1-s)&gt;s$ when $m&lt;1$. Thus one is the only fixed point. When $m=1$ and the law is not concentrated at one, it assigns positive probability to some $k\geq2$, where the same inequality is strict. Again $\phi(s)&gt;s$ for $s&lt;1$. The deterministic exception is immediate from the recursion. Finally, if $m&gt;1$, the left derivative $\phi'(1)=m$ implies $\phi(s)-s&lt;0$ for $s&lt;1$ sufficiently close to one. Since $\phi(0)\geq0$, continuity gives a fixed point below one, so the least fixed point is below one.</p><p>The <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L309">notes' extinction statement</a> omits the deterministic critical exception. It is recorded as N-ERR-03 in the source audit; the statement here includes it explicitly.</p>

## Expected total progeny {#section-expectation}

<a id="tag-UKY4" data-assertion="proposition" data-title="Mean generation sizes and expected total progeny"></a><p>For every $n\geq0$, $\mathbb E Z_n=m^n$. Consequently</p><div class="math-display">$$\mathbb E T=\begin{cases}(1-m)^{-1},&amp;m&lt;1,\\ \infty,&amp;m\geq1.\end{cases}$$</div><p><em>Proof.</em> Conditional on the population in generation $n$, its members have mean $m$ offspring each. Thus $\mathbb E[Z_{n+1}\mid Z_n]=mZ_n$, and induction gives the generation means. Tonelli's theorem then gives $\mathbb E T=\sum_{n\geq0}m^n$.</p><p>At a nondegenerate critical law, $T$ is finite almost surely but has infinite expectation. There is no contradiction: extinction determines whether $T$ is finite, not whether its distribution is integrable. The subcritical formula is the branching-process reference for the <a href="#/susceptibility">susceptibility</a> exponent.</p>

## The critical square-root singularity {#section-critical-transform}

<a id="tag-OVG9" data-assertion="proposition" data-title="Critical total-progeny generating-function asymptotic"></a><p>Suppose $m=1$ and $0&lt;\sigma^2=\operatorname{Var}(\xi)&lt;\infty$. Let $F(s)=\mathbb E[s^T]$. Then, as $s\uparrow1$,</p><div class="math-display">$$1-F(s)\sim\sqrt{\frac{2(1-s)}{\sigma^2}}.$$</div><p><em>Proof.</em> Extinction is almost sure, so $T&lt;\infty$ almost surely and $F(s)\uparrow1$. Decomposing the tree at its root gives $F(s)=s\phi(F(s))$ for $0\leq s&lt;1$. Finite second moment gives</p><div class="math-display">$$\phi(1-u)=1-u+\frac{\sigma^2}{2}u^2+o(u^2).$$</div><p>Indeed, $\phi''(s)=\mathbb E[\xi(\xi-1)s^{\xi-2}]$ for $0&lt;s&lt;1$, with the terms for $\xi&lt;2$ taken as zero. It increases to $\mathbb E[\xi(\xi-1)]=\sigma^2$ as $s\uparrow1$, and integrating twice gives the expansion. Set $t=1-s$ and $u=1-F(s)$. The functional equation becomes</p><div class="math-display">$$t(1-u)=(1-t)\left(\frac{\sigma^2}{2}u^2+o(u^2)\right).$$</div><p>Since $t,u\to0$ and $u&gt;0$ for $s&lt;1$, division by $u^2$ gives $t/u^2\to\sigma^2/2$.</p><p>This is a transform asymptotic. The two-sided tail order is proved below without a Tauberian theorem. The <a href="/tag/PVM9/">exact tail equivalent</a>, $\mathbb P(T\geq n)\sim\sqrt{2/(\pi\sigma^2)}\,n^{-1/2}$, follows from the <a href="/articles/regular-variation/">Laplace–tail theorem</a>. A point-probability asymptotic requires a separate local result with the appropriate lattice support. For the critical law $\mathbb P(\xi=0)=\mathbb P(\xi=2)=1/2$, every finite family tree has odd total size: its number of edges is twice its number of parents, while also equalling $T-1$. Hence $\mathbb P(T=n)=0$ for every even $n$. This is the support obstruction recorded as N-ERR-04; the <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L365">notes' unqualified all-integer point-probability estimate</a> cannot hold for this law.</p>


## Critical survival to generation n {#section-generation-survival}

<a id="tag-8WO7" data-assertion="proposition" data-title="Critical survival probability with finite nonzero variance"></a><p>Under the same assumptions $m=1$ and $0&lt;\sigma^2&lt;\infty$,</p><div class="math-display">$$\mathbb P(Z_n&gt;0)\sim\frac{2}{\sigma^2 n}.$$</div><p><em>Proof.</em> Write $r_n=\mathbb P(Z_n&gt;0)$. Extinction gives $r_n\downarrow0$, and the offspring decomposition gives $r_{n+1}=1-\phi(1-r_n)$. The second-order expansion therefore yields</p><div class="math-display">$$r_{n+1}=r_n-\frac{\sigma^2}{2}r_n^2+o(r_n^2).$$</div><p>Each $r_n$ is positive: the offspring law gives positive probability to at least one child, and a lineage can continue for any fixed finite number of generations. Since $r_{n+1}/r_n\to1$,</p><div class="math-display">$$\frac1{r_{n+1}}-\frac1{r_n}=\frac{r_n-r_{n+1}}{r_nr_{n+1}}\longrightarrow\frac{\sigma^2}{2}.$$</div><p>Summing these increments and taking their arithmetic mean gives $1/(nr_n)\to\sigma^2/2$.</p>

## Population size conditional on survival {#section-yaglom}

<a id="tag-AYHV" data-assertion="theorem" data-title="Yaglom's exponential population limit with finite offspring variance"></a>
<p>For a Galton–Watson process started from one ancestor, suppose $\mathbb E\xi=1$ and $0&lt;\sigma^2=\operatorname{Var}(\xi)&lt;\infty$. Put $a=\sigma^2/2$. Conditional on $Z_n&gt;0$,</p>
<div class="math-display">$$\frac{Z_n}{n}\ \Longrightarrow\ Y,\qquad
\mathbb P(Y&gt;x)=e^{-x/a}\quad(x\geq0).$$</div>
<p>The conditional means also converge to $a$, and the conditional laws of $Z_n/n$ are uniformly integrable. No third moment or aperiodicity assumption is needed.</p>
<p><em>Proof.</em> Write $\phi$ for the offspring generating function and $Q_n=\mathbb P(Z_n&gt;0)$. Fix $\lambda&gt;0$, and for $0\leq k\leq n$ set</p>
<div class="math-display">$$u_{k,n}=1-\mathbb E[e^{-\lambda Z_k/n}].$$</div>
<p>The branching property gives $u_{k+1,n}=1-\phi(1-u_{k,n})$, starting at $u_{0,n}=1-e^{-\lambda/n}$. Criticality implies $0&lt;u_{k,n}\leq u_{0,n}$, and the finite-variance expansion gives</p>
<div class="math-display">$$\frac1{u_{k+1,n}}-\frac1{u_{k,n}}=a+o(1),$$</div>
<p>where the error is uniform in $0\leq k&lt;n$: every argument is at most $u_{0,n}\to0$. Summing yields $1/u_{n,n}=1/u_{0,n}+n(a+o(1))$, hence</p>
<div class="math-display">$$nu_{n,n}\longrightarrow\frac{\lambda}{1+a\lambda}.$$</div>
<p>By <a href="/tag/8WO7/">the survival asymptotic</a>, $nQ_n\to1/a$. Removing the mass at zero therefore gives</p>
<div class="math-display">$$\mathbb E[e^{-\lambda Z_n/n}\mid Z_n&gt;0]
=1-\frac{u_{n,n}}{Q_n}\longrightarrow\frac1{1+a\lambda}.$$</div>
<p>The limiting Laplace transform is that of the stated exponential law and is continuous at zero, proving weak convergence. Since $\mathbb E Z_n=1$, the conditional mean is $1/(nQ_n)\to a=\mathbb E Y$. For nonnegative laws, weak convergence together with convergence of these means implies uniform integrability: subtract the convergent expectations of $\min(Z_n/n,K)$ from the means, then send $K\to\infty$.</p>
<p>The normalization concerns population in one generation, rather than total progeny. In particular, the exponential limit here and the <a href="/tag/0OEW/">size-biased finite-progeny limit</a> describe different observables.</p>

## Total-progeny tail order {#section-progeny-tail}

<a id="tag-MIFH" data-assertion="proposition" data-title="Critical total-progeny tail has order inverse square root"></a><p>If $m=1$ and $0&lt;\sigma^2&lt;\infty$, there are constants $c,C&gt;0$ such that, for all sufficiently large integers $n$,</p><div class="math-display">$$c n^{-1/2}\leq\mathbb P(T\geq n)\leq C n^{-1/2}.$$</div><p><em>Proof.</em> Set $G(t)=\mathbb E[1-e^{-tT}]$. The transform asymptotic and $1-e^{-t}\sim t$ give $G(t)\sim a\sqrt t$, where $a=\sqrt{2/\sigma^2}$. On $\{T\geq n\}$, $1-e^{-T/n}\geq1-e^{-1}$, so</p><div class="math-display">$$\mathbb P(T\geq n)\leq\frac{G(1/n)}{1-e^{-1}}\leq C n^{-1/2}.$$</div><p>Increasing $C$ if necessary makes the bound hold for every $n\geq1$. For a fixed large constant $L$, split according to $T&lt;n$ and $T\geq n$ and use $1-e^{-x}\leq x$:</p><div class="math-display">$$G\!\left(\frac1{Ln}\right)\leq\frac{\mathbb E[T\wedge n]}{Ln}+\mathbb P(T\geq n)\leq\frac{2C}{L\sqrt n}+\mathbb P(T\geq n).$$</div><p>The last step uses $\mathbb E[T\wedge n]=\sum_{k=1}^n\mathbb P(T\geq k)\leq2C\sqrt n$. For sufficiently large $n$, the left-hand side is at least $a/(2\sqrt{Ln})$. Choose $\sqrt L&gt;4C/a$; subtracting the first term leaves a positive constant times $n^{-1/2}$. This proves the lower bound without a local limit theorem and is compatible with periodic support.</p>

## A near-critical thinning family {#section-thinning}

<a id="tag-XXQK" data-assertion="proposition" data-title="Near-critical survival under independent offspring thinning"></a>
<p>Let $\eta$ be a nonnegative integer-valued random variable with $\mu=\mathbb E\eta&gt;1$ and $\mathbb E\eta^2&lt;\infty$. Write $\nu=\mathbb E[\eta(\eta-1)]$. For $p\in[0,1]$, let $\xi_p$, conditional on $\eta$, have distribution $\operatorname{Binomial}(\eta,p)$, and let $\rho(p)$ be the survival probability of the Galton–Watson process with offspring law $\xi_p$. Then $0&lt;\nu&lt;\infty$, the threshold is $p_c=1/\mu$, and</p>
<div class="math-display">$$\rho(p)=0\quad(p\leq p_c),\qquad\rho(p)&gt;0\quad(p&gt;p_c),\qquad\rho(p)\sim\frac{2\mu^3}{\nu}(p-p_c)\quad(p\downarrow p_c).$$</div>
<p><em>Proof.</em> Put $\phi(s)=\mathbb E[s^\eta]$. Conditional binomial expectation gives the offspring generating function $\phi_p(s)=\phi(1-p+ps)$, with mean $p\mu$ and second factorial moment $p^2\nu$. Since $\mu&gt;1$, the law of $\eta$ gives positive mass to some value at least two, so $\nu&gt;0$. At $p_c&lt;1$, the thinned law has $\mathbb P(\xi_{p_c}=0)=\mathbb E[(1-p_c)^\eta]&gt;0$ and is not the deterministic one-child law. The <a href="/tag/BFM4/">extinction criterion</a> therefore gives the first two assertions, including extinction at the threshold.</p>
<p>Let $q(p)=1-\rho(p)$. By the <a href="/tag/8TFY/">fixed-point characterization</a>, $q(p)=\phi(1-p+pq(p))$. As $p\downarrow p_c$, every subsequential limit $q_*$ of $q(p)$ satisfies $q_*=\phi(1-p_c+p_cq_*)$, by continuity. The critical offspring generating function has no fixed point below one, so $q_*=1$. Compactness of $[0,1]$ now gives $\rho(p)\to0$.</p>
<p>Finite second moment gives $\phi''(s)\uparrow\nu$ as $s\uparrow1$. Integrating twice yields the expansion</p>
<div class="math-display">$$\phi(1-t)=1-\mu t+\frac\nu2t^2+o(t^2).$$</div>
<p>Apply it with $t=p\rho(p)$ in the extinction equation. For $p&gt;p_c$ the survival probability is positive, so division by it gives</p>
<div class="math-display">$$\mu p-1=\frac\nu2p^2\rho(p)+o(\rho(p)).$$</div>
<p>Since $p\to1/\mu$ and $\nu&gt;0$, this implies $\rho(p)/(\mu p-1)\to2\mu^2/\nu$, proving the stated equivalent.</p>
<p>The critical offspring variance is $\sigma_c^2=p_c^2\nu$, so the same equivalent reads $\rho(p)\sim2(p\mu-1)/\sigma_c^2$. Below criticality the existing <a href="/tag/UKY4/">total-progeny expectation</a> is exactly $(1-p\mu)^{-1}$. For a deterministic potential offspring count $\eta=2$, the survival coefficient is eight, agreeing with the <a href="/articles/binary-tree-percolation/">binary-tree formula</a> at $p_c=1/2$.</p>
<p>This is a precise family version of the near-critical calculation in the preliminary notes, lines 333–346. It uses an $o(t^2)$ remainder from one fixed generating function, not an $O(t^3)$ remainder requiring a third-moment bound. For an arbitrary family of offspring laws whose mean approaches one, pointwise finite second moments alone do not supply the uniform Taylor control or convergence of extinction roots used here.</p>

## Varying the offspring law {#section-varying-laws}

<a id="tag-N9P5" data-assertion="proposition" data-title="Near-critical survival with uniformly integrable squared offspring"></a>
<p>Let $\xi_j$ be nonnegative integer-valued offspring variables with means $m_j&gt;1$ tending to one. Suppose $\xi_j$ converges in distribution to $\xi$, where $\mathbb E\xi=1$ and $0&lt;\sigma^2=\operatorname{Var}(\xi)&lt;\infty$, and suppose their squares are uniformly integrable:</p>
<div class="math-display">$$\lim_{R\to\infty}\sup_j\mathbb E[\xi_j^2\mathbf1_{\{\xi_j&gt;R\}}]=0.$$</div>
<p>If $\rho_j$ is the survival probability for offspring law $\xi_j$, then</p>
<div class="math-display">$$\rho_j\sim\frac{2(m_j-1)}{\sigma^2}\sim\frac{2(m_j-1)}{\mathbb E[\xi_j(\xi_j-1)]}.$$</div>
<p><em>Proof.</em> Write $\phi_j(s)=\mathbb E[s^{\xi_j}]$ and $\phi(s)=\mathbb E[s^\xi]$. Convergence in distribution gives pointwise convergence of these generating functions on $[0,1]$. Also $|\phi_j(s)-\phi_j(t)|\leq m_j|s-t|$, and the means are bounded. Thus whenever $s_j\to s$, we have $\phi_j(s_j)\to\phi(s)$. Every subsequential limit of the extinction probabilities $q_j=1-\rho_j$ is consequently a fixed point of $\phi$. The limiting law is critical and nondegenerate, so its only fixed point is one. It follows that $\rho_j\to0$.</p>
<p>Put $b_j=\mathbb E[\xi_j(\xi_j-1)]$. Truncating the expectations at a fixed integer $R$ and using uniform integrability on the remaining tail gives $b_j\to\mathbb E[\xi(\xi-1)]=\sigma^2$. The same truncation makes the second-order expansion uniform. Indeed, with the summands for $\xi_j&lt;2$ understood as zero,</p>
<div class="math-display">$$0\leq b_j-\phi_j''(1-u)=\mathbb E\!\left[\xi_j(\xi_j-1)\bigl(1-(1-u)^{\xi_j-2}\bigr)\right].$$</div>
<p>On $\{\xi_j\leq R\}$ the expression is bounded by $R^2[1-(1-u)^R]$, independently of $j$; the complementary expectation is bounded by $\mathbb E[\xi_j^2\mathbf1_{\{\xi_j&gt;R\}}]$. First choose $R$ large, then let $u\downarrow0$. Integrating twice therefore gives, uniformly in $j$,</p>
<div class="math-display">$$\phi_j(1-u)=1-m_ju+\frac{b_j}{2}u^2+o(u^2).$$</div>
<p>Insert $u=\rho_j$ into $1-\rho_j=\phi_j(1-\rho_j)$. Since $m_j&gt;1$, the extinction criterion gives $\rho_j&gt;0$, and division by $\rho_j$ yields $m_j-1=(b_j/2+o(1))\rho_j$. The two equivalents follow from $b_j\to\sigma^2&gt;0$.</p>
<p>No coupling or monotonicity of the offspring laws is required. Independent thinning of one square-integrable potential offspring variable satisfies the tail condition because the thinned count is bounded by that variable. A uniform moment bound of order $2+\delta$, for any $\delta&gt;0$, is another sufficient condition, since its squared tail is at most $R^{-\delta}\sup_j\mathbb E\xi_j^{2+\delta}$.</p>

<a id="tag-Q4NA" data-assertion="proposition" data-title="Finite second moments alone do not imply a near-critical survival asymptotic"></a>
<p>For integers $j\geq2$, let $\xi_j=j$ with probability $1/[j(j-1)]$ and $\xi_j=1$ otherwise. Then</p>
<div class="math-display">$$m_j=1+\frac1j,\qquad\mathbb E[\xi_j(\xi_j-1)]=1,\qquad\mathbb E\xi_j^2=2+\frac1j,\qquad\rho_j=1.$$</div>
<p><em>Proof.</em> The moment formulas follow directly from the two masses. Every individual has at least one child, so the process never becomes extinct. Thus the expression $2(m_j-1)/\mathbb E[\xi_j(\xi_j-1)]=2/j$ tends to zero although survival is certain. Here $\xi_j$ converges to the deterministic one-child law, and the squares are not uniformly integrable: for $j&gt;R$, their tail expectation is $j/(j-1)$. Even bounded second moments and a positive limiting second factorial moment do not prevent the second moment from escaping to increasingly rare large offspring counts.</p>
<p>These statements make explicit the family hypotheses behind the <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L333">notes' near-critical expansion, lines 333–346</a>. The example does not contradict the expansion for one fixed generating function; it prevents applying that expansion uniformly to an arbitrary varying family.</p>

## The joint mean and ghost-field limit {#section-crossover}

<a id="tag-DGVA" data-assertion="theorem" data-title="Near-critical total-progeny ghost crossover with uniformly integrable squared offspring"></a>
<p>Let $\xi_j$ be nonnegative integer-valued offspring variables converging in distribution to $\xi$, where $\mathbb E\xi=1$ and $0&lt;\sigma^2=\operatorname{Var}(\xi)&lt;\infty$. Assume that $(\xi_j^2)$ is uniformly integrable. Put $\varepsilon_j=\mathbb E\xi_j-1$, let $T_j$ be the total progeny from one ancestor, and, for $h&gt;0$, set</p>
<div class="math-display">$$M_j(h)=1-\mathbb E[e^{-hT_j};\,T_j&lt;\infty].$$</div>
<p>Thus infinite progeny contributes one to the ghost probability. For every sequence $h_j&gt;0$ tending to zero,</p>
<div class="math-display">$$M_j(h_j)\sim
\frac{\varepsilon_j+\sqrt{\varepsilon_j^2+2\sigma^2h_j}}{\sigma^2}.$$
</div>
<p>The means may approach one from either side or equal one. No relation between the rates of decay of $h_j$ and $\varepsilon_j^2$ is assumed.</p>
<p><em>Proof.</em> Write $\phi_j$ for the offspring generating function. Root decomposition gives</p>
<div class="math-display">$$1-M_j(h)=e^{-h}\phi_j(1-M_j(h)).$$</div>
<p>The bounded-mean continuity argument in <a href="/tag/N9P5/">N9P5</a> applies without the supercritical restriction: every subsequential limit of $1-M_j(h_j)$ is a fixed point of the limiting critical generating function. Its only fixed point is one, so $u_j=M_j(h_j)\to0$. Uniform integrability gives $\varepsilon_j\to0$ and, by the same truncated second-derivative argument,</p>
<div class="math-display">$$\phi_j(1-u_j)=1-(1+\varepsilon_j)u_j+a_ju_j^2,
\qquad a_j\longrightarrow\sigma^2/2.$$</div>
<p>Multiplying the root equation by $e^{h_j}$ now gives the exact relation</p>
<div class="math-display">$$a_ju_j^2-\varepsilon_ju_j
=(e^{h_j}-1)(1-u_j)=c_jh_j,\qquad c_j\longrightarrow1.$$</div>
<p>This quadratic comparison remains stable when the positive root is much smaller than $|\varepsilon_j|$. To see this directly, let $r_j&gt;0$ solve $(\sigma^2/2)r_j^2-\varepsilon_jr_j=h_j$. If $a_j/(\sigma^2/2)$ and $c_j$ lie in $[1-\eta,1+\eta]$, substitution into the two bounding quadratics gives</p>
<div class="math-display">$$\frac{1-\eta}{1+\eta}r_j\leq u_j\leq
\frac{1+\eta}{1-\eta}r_j\qquad(0&lt;\eta&lt;1).$$</div>
<p>Each quadratic has exactly one positive root, since its constant term is negative. Letting $\eta\downarrow0$ proves the equivalent, uniformly in the sign and relative size of $\varepsilon_j$.</p>
<p>If $\varepsilon_j^2=o(h_j)$, this is the critical square-root law $M_j(h_j)\sim\sqrt{2h_j/\sigma^2}$. If $h_j=o(\varepsilon_j^2)$, it gives $M_j(h_j)\sim h_j/|\varepsilon_j|$ on the subcritical side and $M_j(h_j)\sim2\varepsilon_j/\sigma^2$ on the supercritical side. The latter is the survival contribution. These are positive-field limits: with the literal empty ghost field, $M_j(0)=0$, while $M_j(0+)=\mathbb P(T_j=\infty)$.</p>
<p>The <a href="/articles/size-biased-laws/#section-branching-cutoff">finite-progeny scaling law</a> below isolates the finite clusters on both sides. The crossover is a transform statement; it does not assert an all-integer local probability estimate.</p>

## Exact finite-progeny probabilities {#section-dwass}

<a id="tag-RL1L" data-assertion="theorem" data-title="Dwass's formula for total progeny from one ancestor"></a>
<p>For independent copies $\xi_1,\ldots,\xi_n$ of the offspring variable and each integer $n\geq1$,</p>
<div class="math-display">$$\mathbb P(T=n)=\frac1n\mathbb P\!\left(\sum_{i=1}^n\xi_i=n-1\right).$$</div>
<p>The identity holds on either side of criticality. If survival has positive probability, it describes the finite part of the total-progeny law.</p>
<p><em>Proof.</em> Explore the family tree one individual at a time, placing its children at the end of the queue. Before the queue first empties, its size after $k$ individuals have been explored is $1+S_k$, where $S_0=0$ and $S_k=\sum_{i=1}^k(\xi_i-1)$. The unexplored offspring counts are independent with the original law, so they may be sampled in advance as an infinite independent sequence. Hence $T=n$ exactly when $S_k\geq0$ for $k&lt;n$ and $S_n=-1$.</p>
<p>Fix an integer sequence $a_1,\ldots,a_n$ with $a_i\geq-1$ and sum $-1$, and write $s_k=\sum_{i=1}^ka_i$. Exactly one of its $n$ cyclic starting positions has all its proper partial sums nonnegative. To see this, let $j$ be the first index attaining the minimum of $s_0,\ldots,s_{n-1}$, and start after $j$. Before wrapping around, the proper sums are $s_i-s_j\geq0$. If $j&gt;0$, then $s_j\leq-1$, so the sum at the old endpoint is $-1-s_j\geq0$. After wrapping, a proper sum has the form $-1-s_j+s_i$ with $i&lt;j$; this is nonnegative because $s_i&gt;s_j$ and both are integers. Conversely, nonnegative proper sums for a start after $j$ force $s_i\geq s_j$ for later indices and $s_i&gt;s_j$ for earlier ones. Thus $j$ must be precisely that first minimum.</p>
<p>Apply this observation to $a_i=\xi_i-1$. The joint law is invariant under each cyclic rotation. On the event $S_n=-1$, the sum of the indicators that the $n$ starting positions give a valid queue path is one; outside that event it is zero. Taking expectations, each of the $n$ indicators has expectation $\mathbb P(T=n)$, which proves the formula. This counts starting positions, so no assumption that the rotations are distinct is needed.</p>

<a id="tag-AGPB" data-assertion="corollary" data-title="Exact periodic progeny law for zero-or-two offspring"></a>
<p>If $\mathbb P(\xi=0)=\mathbb P(\xi=2)=1/2$, then for $k\geq0$,</p>
<div class="math-display">$$\mathbb P(T=2k+1)=\frac{1}{k+1}\binom{2k}{k}2^{-(2k+1)},\qquad\mathbb P(T=2k+2)=0.$$</div>
<p>Consequently, along odd $n\to\infty$,</p>
<div class="math-display">$$\mathbb P(T=n)\sim\sqrt{\frac2\pi}\,n^{-3/2},$$</div>
<p>whereas over all integers $n\to\infty$,</p>
<div class="math-display">$$\mathbb P(T\geq n)\sim\sqrt{\frac2\pi}\,n^{-1/2}.$$</div>
<p><em>Proof.</em> A sum of $n$ offspring counts is even, so Dwass's formula vanishes for even $n$. For $n=2k+1$, it requires exactly $k$ of those counts to equal two and gives $(2k+1)^{-1}\binom{2k+1}{k}2^{-(2k+1)}$, which is the displayed Catalan expression. Stirling's formula makes this asymptotic to $1/(2\sqrt\pi\,k^{3/2})$, giving the odd-size equivalent. Critical extinction leaves no mass at infinity. Summing over $k\geq\lceil(n-1)/2\rceil$ and using $\sum_{k\geq K}k^{-3/2}\sim2K^{-1/2}$ gives the tail equivalent.</p>
<p>This calculation resolves the support issue in the <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L365">notes' local-probability claim</a> without assuming a local limit theorem. The point-mass equivalent holds only on odd sizes, but the tail equivalent holds on all sizes. The offspring law here differs from the $\operatorname{Binomial}(2,1/2)$ law of the critical <a href="/articles/binary-tree-percolation/">binary-tree percolation cluster</a>, which permits one child and has no such parity restriction.</p>

## Conditioned plane trees and contours {#section-contours}

<a id="tag-NT0R" data-assertion="proposition" data-title="Conditioned plane-tree weights and the geometric contour law"></a>
<p>For a finite rooted ordered tree $t$, let $d_t(v)$ count the children of $v$. A Galton–Watson tree with offspring law $\mu$ has</p>
<div class="math-display">$$\mathbb P(\mathcal T=t)=\prod_{v\in t}\mu(d_t(v)).$$</div>
<p>Conditioning on $T=n$ divides these weights by $\mathbb P(T=n)$, when positive. For $\mu(k)=2^{-k-1}$, the conditioned tree is uniform among ordered trees with $n$ vertices. Its depth-first contour, recording distance from the root while traversing each edge in both directions, is uniform among nonnegative simple-walk bridges of length $2(n-1)$.</p>
<p><em>Proof.</em> Independence gives the product. Since $\sum_v d_t(v)=n-1$, the geometric weight is $2^{-(2n-1)}$, independent of shape. Contours correspond bijectively to nonnegative bridges: an upward step creates the next child; a downward step returns to its parent. Each bridge has the same simple-random-walk probability.</p>
<p>General offspring laws need not give uniform contours. For zero-or-two offspring and $n=3$, only the two-leaf tree is possible, whereas the three-vertex chain is another ordered tree.</p>
<p>The <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L473">notes' continuum-tree discussion</a> requires a separate limit theorem. <a href="https://arxiv.org/pdf/math/0511515v1">Le Gall, Theorem 1.15 and §1.6</a>, uses an exponential-moment assumption in its proof and $\mu(1)&gt;0$ to permit conditioning at every size. Neither contour convergence nor diameter scaling is proved here.</p>

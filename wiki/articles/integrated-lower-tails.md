---
{
  "id": "integrated-lower-tails",
  "title": "Integrated lower tails from moment bounds",
  "subtitle": "Choosing the susceptibility scale before truncating",
  "kind": "method",
  "category": "Methods",
  "summary": "A first/second-moment estimate retains a fixed fraction of the mean below a suitable cutoff. A continuous unbounded family of means and a cubic moment bound then give a square-root lower bound at a dominating endpoint law.",
  "context": ["Nonnegative random variables with finite positive first moment and finite second moment.", "The family theorem assumes a continuous unbounded mean and stochastic domination by an endpoint variable.", "Percolation sharpness, moment bounds and parameter continuity are separate inputs to that application."],
  "related": ["susceptibility", "sharpness", "universal-tightness", "cutoff-families"],
  "sourceIds": ["notes"],
  "aliases": ["integrated lower tail", "Aizenman-Barsky", "truncated mean", "moment ratio", "critical volume tail"],
  "prototypeUses": []
}
---

## Retaining part of the mean {#section-truncation}

<a id="tag-LLGA" data-assertion="proposition" data-title="Truncated mean bound at the second-to-first moment scale"></a><p>Let $X\geq0$ have $\mu=\mathbb E X\in(0,\infty)$ and $\nu=\mathbb E X^2&lt;\infty$. For every $\lambda&gt;1$,</p><div class="math-display">$$\mathbb E\!\left[X\mathbf1_{\{X\leq\lambda\nu/\mu\}}\right]\geq(1-\lambda^{-1})\mu,\qquad \mathbb E[X\wedge N]\geq(1-\lambda^{-1})\mu\quad\text{if }N\geq\lambda\nu/\mu.$$</div><p><em>Proof.</em> With $L=\lambda\nu/\mu&gt;0$, the pointwise bound $X\mathbf1_{\{X&gt;L\}}\leq X^2/L$ gives</p><div class="math-display">$$\mathbb E[X\mathbf1_{\{X&gt;L\}}]\leq\frac\nu L=\frac\mu\lambda.$$</div><p>Subtract this from $\mathbb E X$. For $N\geq L$, $X\wedge N\geq X\mathbf1_{\{X\leq L\}}$, proving the second assertion.</p><p>The ratio $\nu/\mu$ is the mean under volume bias, but this proof needs only the displayed moment estimate. It bounds the mass retained by truncation; it does not say that $X$ is usually close to its mean.</p>

## Interpolating to an endpoint law {#section-family}

<a id="tag-F75G" data-assertion="theorem" data-title="Conditional integrated square-root lower bound from cubic moments"></a><p>Let $I=[t_0,t_c)$ be a nonempty real interval, allowing $t_c=\infty$. For $t\in I$, let $X_t\geq0$ satisfy</p><div class="math-display">$$0&lt;\mu(t)=\mathbb E X_t&lt;\infty,\qquad \mathbb E X_t^2\leq C\mu(t)^3$$</div><p>for a fixed $C&gt;0$. Suppose $\mu$ is continuous and unbounded on $I$, and suppose a nonnegative extended random variable $X_*$ stochastically dominates every $X_t$. Then, for every real $N\geq2C\mu(t_0)^2$,</p><div class="math-display">$$\mathbb E[X_*\wedge N]\geq\frac1{2\sqrt{2C}}\sqrt N.$$</div><p>If $X_*$ is integer-valued, allowing infinity, this gives for every integer $N$ in the same range</p><div class="math-display">$$\sum_{n=1}^N\mathbb P(X_*\geq n)\geq\frac1{2\sqrt{2C}}\sqrt N.$$</div><p><em>Proof.</em> Continuity and unboundedness allow a choice of $t\in I$ with $\mu(t)=\sqrt{N/(2C)}$: take a parameter with mean above the target and apply the intermediate value theorem between it and $t_0$. At this parameter,</p><div class="math-display">$$\frac{2\mathbb E X_t^2}{\mu(t)}\leq2C\mu(t)^2=N.$$</div><p>The truncation bound with $\lambda=2$ gives $\mathbb E[X_t\wedge N]\geq\mu(t)/2$. Stochastic domination gives $\mathbb E[X_*\wedge N]\geq\mathbb E[X_t\wedge N]$, proving the first claim. For integer-valued $X_*$, apply the <a href="/tag/CSY8/">tail-sum identity</a> to $X_*\wedge N$.</p><p>Only continuity of the first moment was used. There is no assumption that the second moment, or its ratio to the first moment, varies continuously. Unboundedness also need not be monotone for the intermediate-value argument, although percolation couplings normally provide monotonicity.</p>

## The percolation application and its inputs {#section-percolation}

<p>For a root cluster below a critical parameter, take $X_t=|K_o|$ under the parameter-$t$ law and $X_*$ to be its critical-law counterpart. A monotone coupling supplies endpoint domination. To apply the theorem with $C=1$, one must also establish finite subcritical susceptibility, continuity and unboundedness of that susceptibility, and the tree-graph second-moment bound</p><div class="math-display">$$\mathbb E_t|K_o|^2\leq\chi(t)^3.$$</div><p>The abstract theorem then gives the integrated lower bound with constant $1/(2\sqrt2)$. It does not establish those inputs, choose the correct critical parameter for a model, or show that the endpoint law exists in a given parametrization. In particular, finiteness of susceptibility at each subcritical parameter alone does not supply its unboundedness or continuity.</p><p>The <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L1365">integrated lower-tail section of the notes, including S007</a>, uses the same truncation estimate and chooses the moment-ratio scale. The argument here instead chooses the susceptibility scale directly, so it avoids the additional continuity claim about that ratio. This is a conditional formulation of the proof mechanism, rather than an unconditional assertion for every transitive weighted graph.</p><p>The conclusion concerns a sum of tail probabilities. It should not be reported as a pointwise lower bound $\mathbb P(X_*\geq N)\geq cN^{-1/2}$: the truncation estimate and interpolation argument do not prove that statement. Nor is $\mathbb E[X_*\wedge N]$ the susceptibility with the infinite-cluster contribution deleted; it retains the value $N$ on $\{X_*=\infty\}$.</p>

## Critical integrated tails and a bounded field range {#section-critical-field}

<a id="tag-36PN" data-assertion="theorem" data-title="Universal integrated critical tail and saturated square-root field lower bound"></a>
<p>Consider independent bonds on a nonempty countable vertex set, with symmetric finite nonnegative off-diagonal weights preserved by a transitive group and probabilities $1-e^{-\beta J(x,y)}$. Assume $0&lt;L=\sum_{y\ne o}J(o,y)&lt;\infty$ and $\beta_c&lt;\infty$. At criticality write $T=|K_o|$, allowing $T=\infty$, and $M(h)=\mathbb E_{\beta_c}[1-e^{-hT}]$ for $h&gt;0$. Then</p>
<div class="math-display">$$\mathbb E_{\beta_c}[T\wedge N]\geq\frac{\sqrt N}{2\sqrt2}\qquad(N\geq1),$$</div>
<p>and, for every $h&gt;0$,</p>
<div class="math-display">$$M(h)\geq\frac{1-e^{-1}}{2\sqrt2}\min\{\sqrt h,1\}.$$</div>
<p><em>Proof.</em> The row-sum bound gives $\beta_c\geq1/L&gt;0$. The <a href="/articles/integrated-susceptibility/#section-finite-set">finite-set sharpness proof</a> gives finite susceptibility below $\beta_c$, and <a href="/tag/5LNL/">right-openness and endpoint divergence</a> give $\chi_\beta\uparrow\infty$ as $\beta\uparrow\beta_c$. Susceptibility is continuous on $[0,\beta_c)$: the quantitative right-openness estimate gives right-continuity, while monotone coupling and finite path witnesses give left-continuity. At zero, $\chi_0=1$.</p>
<p>Transitivity and the <a href="/tag/Y84V/">tree-graph bound</a> give $\mathbb E_\beta|K_o|^2\leq\chi_\beta^3$ below criticality. The critical cluster volume stochastically dominates all these subcritical volumes. Apply <a href="/tag/F75G/">the interpolation theorem</a> with $t_0=0$ and cubic-moment constant one. It gives the first bound for $N\geq2$. For $1\leq N&lt;2$, use $T\geq1$.</p>
<p>Concavity on $[0,1]$ and monotonicity afterwards give $1-e^{-t}\geq(1-e^{-1})\min\{t,1\}$ for $t\geq0$. Thus for $0&lt;h\leq1$, including the infinite-cluster contribution,</p>
<div class="math-display">$$M(h)\geq(1-e^{-1})h\,\mathbb E_{\beta_c}[T\wedge h^{-1}]\geq\frac{1-e^{-1}}{2\sqrt2}\sqrt h.$$</div>
<p>For $h\geq1$, monotonicity gives $M(h)\geq M(1)$, completing the proof.</p>
<p>This supplies the percolation inputs left explicit in S007 of the notes for the stated countable transitive summable model with finite critical intensity. The integrated bound is not, by itself, a pointwise lower bound on $\mathbb P_{\beta_c}(T\geq N)$, and it does not imply $T&lt;\infty$ almost surely.</p>
<p>The field conclusion gives a small-field form of <a href="https://arxiv.org/pdf/1502.03050v3#page=5">Proposition 1.3 of arXiv:1502.03050v3</a> under explicit hypotheses. Its printed all-positive-field square-root bound cannot hold literally, since $M(h)\leq1$. Saturation makes the displayed conclusion valid for every positive field. This proof uses moment interpolation; it does not establish the source's separate parameter-derivative inequality.</p>


## Recovering a pointwise lower bound {#section-pointwise}

<a id="tag-MBV2" data-assertion="proposition" data-title="Pointwise square-root lower tail from integrated lower and pointwise upper bounds"></a>
<p>Let $(p_n)_{n\geq1}$ be a nonnegative nonincreasing sequence. Suppose that for constants $c,C&gt;0$ and an integer $N_0\geq1$,</p>
<div class="math-display">$$\sum_{k=1}^N p_k\geq c\sqrt N\quad(N\geq N_0),\qquad p_n\leq Cn^{-1/2}\quad(n\geq1).$$</div>
<p>Choose an integer $A\geq2$ such that $c\sqrt A\geq4C$. Then</p>
<div class="math-display">$$p_n\geq\frac{c}{2\sqrt A}\,n^{-1/2}\qquad(n\geq N_0).$$</div>
<p><em>Proof.</em> Apply the integrated bound at $An$. The upper bound controls the first $n$ terms, while monotonicity controls all later terms by $p_n$:</p>
<div class="math-display">$$c\sqrt{An}\leq\sum_{k=1}^{An}p_k\leq C\sum_{k=1}^{n}k^{-1/2}+(A-1)np_n\leq2C\sqrt n+Anp_n.$$</div>
<p>By the choice of $A$, the first term on the right is at most $c\sqrt{An}/2$. Subtract it and divide by $An$.</p>
<p>An eventual pointwise upper bound suffices: increase $C$ to cover the finitely many initial terms. The upper bound is essential to this argument because it prevents the integrated lower bound from being supplied entirely by smaller cluster sizes. No regular variation or differentiability of the tail is used.</p>

## Susceptibility and critical-tail equivalence {#section-equivalence}

<a id="tag-UPMK" data-assertion="theorem" data-title="Equivalence of mean-field susceptibility and endpoint cluster tails"></a>
<p>Consider independent bonds on a nonempty countable vertex set with symmetric finite weights $J(u,v)\geq0$ and probabilities $1-e^{-\beta J(u,v)}$. Suppose a transitive group of vertex permutations preserves the weights, and</p>
<div class="math-display">$$M=\sum_{v\ne o}J(o,v)\in(0,\infty).$$</div>
<p>Let $0\leq a&lt;b&lt;\infty$, with $b&gt;0$, and assume $\chi(\beta)&lt;\infty$ for every $\beta\in(a,b)$ but $\chi(b)=\infty$. Then the following statements are equivalent:</p>
<div class="math-display">$$\chi(\beta)\asymp(b-\beta)^{-1}\quad\text{as }\beta\uparrow b;\qquad \mathbb P_b(|K_o|\geq n)\asymp n^{-1/2}\quad\text{as }n\to\infty.$$</div>
<p>Here $\asymp$ means upper and lower bounds by fixed positive multiples in the indicated limit. In either case there is no infinite cluster at intensity $b$. The endpoint assumptions are explicit; this theorem does not identify $b$ with a percolation threshold.</p>
<p><em>Proof.</em> The <a href="/tag/MXGM/">susceptibility derivative and endpoint argument</a> gives continuity of $\chi$ on $(a,b)$, divergence as $\beta\uparrow b$, and</p>
<div class="math-display">$$\chi(\beta)\geq\frac1{M(b-\beta)}\qquad(a&lt;\beta&lt;b).$$</div>
<p>Choose $\beta_0\in(a,b)$. The <a href="/tag/Y84V/">tree-graph bound</a> gives $\mathbb E_\beta|K_o|^2\leq\chi(\beta)^3$ on $[\beta_0,b)$. Monotone coupling makes the endpoint cluster size dominate every earlier one. Thus <a href="/tag/F75G/">interpolation to an endpoint law</a> applies with cubic-moment constant one, giving</p>
<div class="math-display">$$\sum_{k=1}^N\mathbb P_b(|K_o|\geq k)\geq\frac1{2\sqrt2}\sqrt N$$</div>
<p>for all sufficiently large $N$.</p>
<p>Now suppose the susceptibility estimate holds. Its upper bound and the <a href="/tag/QS3L/">entropy comparison corollary</a>, with logarithmic exponent zero, give $\mathbb P_b(|K_o|\geq n)\leq Cn^{-1/2}$ for large $n$. Increase $C$ to cover all $n\geq1$. The preceding proposition upgrades the integrated lower bound to a matching pointwise lower bound. The upper bound tends to zero, so the endpoint cluster is almost surely finite.</p>
<p>Conversely, a square-root endpoint tail upper bound is uniform in the root by transitivity. The <a href="/tag/1EJP/">tail-to-susceptibility theorem</a> gives $\chi(\beta)\leq C'/(b-\beta)$ for $0&lt;\beta&lt;b$. Combine this with the susceptibility lower bound above. In fact this direction only needs the endpoint upper tail, not its matching lower bound.</p>
<p>This proves the susceptibility/critical-tail part of the notes' equivalence discussion, lines 2503–2558 (S015), and supplies the missing pointwise-upgrade argument. The <a href="#section-four-conditions">four-condition theorem below</a> adds the derivative and second-moment implications, retaining the same endpoint hypotheses.</p>

## The four mean-field conditions {#section-four-conditions}

<a id="tag-9PE0" data-assertion="theorem" data-title="Four equivalent mean-field conditions under explicit endpoint hypotheses"></a>
<p>Under the model and endpoint hypotheses of <a href="/tag/UPMK/">the preceding equivalence theorem</a>, the following four conditions are equivalent:</p>
<div class="math-display">$$\begin{aligned}
\chi(\beta)&\asymp(b-\beta)^{-1}&&\text{as }\beta\uparrow b,\\
\mathbb P_b(|K_o|\geq n)&\asymp n^{-1/2}&&\text{as }n\to\infty,\\
\chi'(\beta)&\asymp\chi(\beta)^2&&\text{for almost every }\beta\text{ sufficiently close to }b\text{ from below},\\
\mathbb E_\beta|K_o|^2&\asymp\chi(\beta)^3&&\text{as }\beta\uparrow b.
\end{aligned}$$</div>
<p>The derivative condition means that fixed positive comparison constants work off a single null set in an interval $(b-\varepsilon_0,b)$. The other parameter-dependent conditions are pointwise on such an interval.</p>
<p><em>Proof.</em> The first two conditions are equivalent by the preceding theorem. The susceptibility condition gives the endpoint lower tail, and <a href="/tag/LZCK/">entropy comparison at the cutoff scale</a> then gives $\mathbb E_\beta|K_o|^2\geq\kappa\chi(\beta)^3$ near $b$ for some $\kappa&gt;0$. The tree-graph bound supplies the opposite inequality. This proves the first condition implies the fourth.</p>
<p>Conversely, suppose the fourth holds. Since $\chi(\beta)\to\infty$ as $\beta\uparrow b$, eventually $\chi\geq4/(c_0\kappa)$. The <a href="/tag/Z9K8/">summed tail derivative bound</a> gives</p>
<div class="math-display">$$\chi'(\beta)\geq\frac{c_0\kappa}{8\beta}\chi(\beta)^2\geq\frac{c_0\kappa}{8b}\chi(\beta)^2$$</div>
<p>almost everywhere sufficiently close to $b$. The universal upper derivative bound $\chi'\leq M\chi^2$ proves the third condition.</p>
<p>Finally, suppose the third condition holds, with lower constant $d&gt;0$. Local absolute continuity of $1/\chi$ gives $(1/\chi)'\leq-d$ almost everywhere near $b$. Integrate from $\beta$ to $t&lt;b$, then let $t\uparrow b$, using $\chi(t)\to\infty$. This yields $1/\chi(\beta)\geq d(b-\beta)$, hence</p>
<div class="math-display">$$\chi(\beta)\leq\frac1{d(b-\beta)}.$$</div>
<p>The universal susceptibility lower bound supplies the reverse estimate and proves the first condition. These implications close the cycle.</p>
<p>This establishes the four-condition mechanism in S015. It assumes finite susceptibility below $b$, divergence at $b$, and a finite positive weight row, and gives derivatives their almost-everywhere meaning. Identifying $b$ with the critical parameter of a particular model still requires the corresponding endpoint and sharpness results. The earlier <a href="/tag/4GNM/">exploration-score inequality</a> gives an additional direct route from the derivative condition to the second-moment lower bound.</p>

---
{
  "id": "stopped-exploration",
  "title": "Stopped cluster exploration",
  "subtitle": "Fair queries on countable graphs and their weighted cost",
  "kind": "method",
  "category": "Methods",
  "summary": "A deterministic priority rule finds n vertices whenever the root cluster contains them. Even when the search never halts, its transcript computes the cluster-tail event and its weighted revealment is bounded by a truncated cluster expectation.",
  "context": ["A countable simple graph with root $o$ and a fixed integer $n\\geq1$.", "Configurations specify the open edges; no independence assumption is needed for the exploration construction.", "For the cost bound, nonnegative edge weights have uniformly bounded sums at each vertex."],
  "related": ["exploration", "finite-transcripts", "connectivity", "susceptibility", "entropy-comparison", "integrated-susceptibility"],
  "sourceIds": ["notes"],
  "aliases": ["stopped exploration", "weighted revealment", "fair exploration", "infinite degree", "cluster tail decision tree"],
  "prototypeUses": []
}
---

## The query rule {#section-rule}

<a id="tag-28UY" data-assertion="definition" data-title="Priority exploration stopped at a cluster-size threshold"></a><p>Fix an injection $\iota:E\to\mathbb N$ ordering the edges of the countable graph. Begin with discovered set $D_0=\{o\}$ and no queried edges. If the discovered set has size $n$, halt. Otherwise, among the unqueried edges incident to the discovered set, query the one of least $\iota$-value. If there is no such edge, halt. An open answer adds both endpoints to the discovered set; a closed answer leaves it unchanged. After halting, record a cemetery symbol at every later step.</p><p>Each query has at least one endpoint already discovered, so it adds at most one vertex. Every discovered vertex is joined to $o$ by previously revealed open edges. Thus $D_t\subseteq K_o$, $|D_t|\leq n$, and the tree never queries an edge twice. Its next query and its stopping decision depend only on the preceding answers. No geometric ordering, finite degree, or transitivity is assumed.</p><p>The priority rule is fair in the following precise sense. Once an edge becomes eligible, it remains eligible until queried unless the tree halts. Only finitely many edges have smaller priority, and none can be queried twice. Hence an eligible edge is eventually queried on any run that continues forever. This is the property that a naive instruction to finish one vertex before moving to the next can lack on an infinite-degree graph.</p>

## What the transcript determines {#section-computation}

<a id="tag-PWBU" data-assertion="proposition" data-title="Stopped exploration Borel-computes the cluster-tail event"></a><p>Let $D_\infty=\bigcup_{t\geq0}D_t$. For every configuration,</p><div class="math-display">$$|D_\infty|=\min\{|K_o|,n\},\qquad \{|K_o|\geq n\}=\{\text{the tree discovers }n\text{ vertices at a finite time}\}.$$</div><p>The right-hand event is a Borel function of the full answer transcript. In particular, the tree Borel-computes the cluster-tail event even if some negative instances run forever.</p><p><em>Proof.</em> If the discovered set reaches size $n$, the statements follow from $D_t\subseteq K_o$. Suppose it never does. If the tree halts, no unqueried edge is incident to its final discovered set. Any open edge incident to that set therefore has both endpoints in it, so the discovered set is the entire root cluster.</p><p>On an infinite run, consider a finite open path from $o$ to any vertex $v\in K_o$. Once a vertex on this path has been discovered, the next path edge either was queried already or becomes eligible. In the first case its open answer already discovered both endpoints; in the second, fairness guarantees a later query and discovery. Induction along the path shows that $v$ is eventually discovered. Thus $D_\infty=K_o$ whenever the threshold is never reached. Since an increasing union of sets of size less than the fixed integer $n$ still has size less than $n$, this also proves the event identity.</p><p>Finally, whether the threshold has been reached by a given time is determined by a finite answer string. The event of ever reaching it is a countable union of finite-prefix cylinders in $\{0,1,\dagger\}^{\mathbb N}$. This gives a single Borel output rule, valid for every configuration and every law.</p><p>Halting is not equivalent to deciding the event through the full transcript. On an infinite star with all edges closed and $n=2$, the cluster is just the root, yet the tree queries forever. Its infinite transcript still gives output zero. Conversely, for $n=1$ the tree stops immediately with output one and asks no questions.</p>

## Weighted revealment {#section-cost}

<a id="tag-DCRV" data-assertion="proposition" data-title="Weighted revealment bounded by truncated cluster size"></a><p>Give the edges finite nonnegative weights $J_e$, and suppose</p><div class="math-display">$$\sum_{e\ni v}J_e\leq M&lt;\infty\qquad\text{for every vertex }v.$$</div><p>If $Q(\omega)$ is the set of all edges queried by the stopped exploration, then, pointwise,</p><div class="math-display">$$\sum_{e\in Q(\omega)}J_e\leq M\min\{|K_o(\omega)|,n\}.$$</div><p>For any probability law $\mu$ on the configuration space with its product sigma-algebra, define $\operatorname{Rev}_\mu(T,e)=\mu(e\in Q)$. Then</p><div class="math-display">$$\sum_{e\in E}J_e\operatorname{Rev}_\mu(T,e)=\mathbb E_\mu\!\left[\sum_{e\in Q}J_e\right]\leq M\mathbb E_\mu[|K_o|\wedge n]\leq Mn.$$</div><p>If $\chi_\mu(o)=\mathbb E_\mu|K_o|$ is finite, the same quantity is also at most $M\chi_\mu(o)$.</p><p><em>Proof.</em> Every queried edge is incident to a discovered vertex, so</p><div class="math-display">$$\sum_{e\in Q}J_e\leq\sum_{v\in D_\infty}\sum_{e\ni v}J_e\leq M|D_\infty|.$$</div><p>Counting an internal edge twice on the right causes no difficulty. Substitute the discovered-set identity above. For each edge, the event that it is queried is a countable union of finite-transcript events and is measurable. Tonelli's theorem therefore turns the expectation of the nonnegative sum into the sum of weighted revealments. No independence or finite expected number of queries is needed: infinitely many queries can have finite total weight.</p><p>On the bond interface, $E$ may be all unordered pairs of distinct vertices, with weight zero on absent edges. The row bound is then $\sum_{w\ne v}J(v,w)\leq M$; diagonal parameters play no role. The finite bound $Mn$ remains available when susceptibility is infinite. It is the truncation, rather than an assumption of subcriticality, that makes this exploration cost finite.</p>

<p>The <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L2266">decision-tree application in the notes</a> uses this weighted cost to compare cluster tails at different intensities. The construction here supplies its countable-graph and Borel-computation details. The entropy inequality now turns this cost into the probability comparison below. Its tail and density consequences require the separately stated susceptibility upper bound.</p>

## Comparing cluster tails {#section-comparison}

<a id="tag-JL1S" data-assertion="theorem" data-title="Cluster-tail comparison from stopped exploration and entropy"></a>
<p>Now let the edges be independent, with probabilities $1-e^{-\beta J_e}$, and retain the uniform weight bound $\sum_{e\ni v}J_e\leq M&lt;\infty$. Write $p_n(\beta)=\mathbb P_\beta(|K_o|\geq n)$ and $\chi(\beta)=\mathbb E_\beta|K_o|$. For $0&lt;\beta_1\leq\beta_2&lt;\infty$ and every integer $n\geq1$,</p>
<div class="math-display">$$\bigl(p_n(\beta_2)-p_n(\beta_1)\bigr)^2\leq\frac{M(\beta_2-\beta_1)^2}{\beta_1}\,p_n(\beta_2)\,\mathbb E_{\beta_1}[|K_o|\wedge n].$$</div>
<p>If $\chi(\beta_1)&lt;\infty$, then</p>
<div class="math-display">$$p_n(\beta_2)\leq\left(\frac2n+\frac{4M(\beta_2-\beta_1)^2}{\beta_1}\right)\chi(\beta_1).$$</div>
<p><em>Proof.</em> The stopped tree Borel-computes the event for every configuration and has finite weighted revealment cost at most $M\mathbb E_{\beta_1}[|K_o|\wedge n]$. Apply the <a href="#/entropy-comparison">weighted entropy comparison</a> in this direction, so the cost is taken at $\beta_1$. Monotonicity gives $p_n(\beta_1)\leq p_n(\beta_2)$, identifying the maximum of the event probabilities and proving the first inequality.</p>
<p>If $p_n(\beta_2)\leq2p_n(\beta_1)$, Markov's inequality gives $p_n(\beta_2)\leq2\chi(\beta_1)/n$. Otherwise $p_n(\beta_2)&gt;0$ and the difference is greater than half of it. The first inequality then gives</p>
<div class="math-display">$$p_n(\beta_2)\leq\frac{4M(\beta_2-\beta_1)^2}{\beta_1}\mathbb E_{\beta_1}[|K_o|\wedge n]\leq\frac{4M(\beta_2-\beta_1)^2}{\beta_1}\chi(\beta_1).$$</div>
<p>Combining the two cases yields the stated bound. No transitivity or finite vertex degree is needed.</p>

## Consequences of a susceptibility upper bound {#section-tail-density}

<a id="tag-QS3L" data-assertion="corollary" data-title="Tail and density upper bounds from mean-field susceptibility control"></a>
<p>In the preceding model, suppose $b\in(0,\infty)$, $C&gt;0$, $a\geq0$, and $0&lt;\varepsilon_0&lt;\min(e^{-1},b/2)$ satisfy</p>
<div class="math-display">$$\chi(b-\varepsilon)\leq C\varepsilon^{-1}\bigl(\log(1/\varepsilon)\bigr)^a\qquad(0&lt;\varepsilon&lt;\varepsilon_0).$$</div>
<p>Then there are finite constants $C_1,C_2$ such that</p>
<div class="math-display">$$\mathbb P_b(|K_o|\geq n)\leq C_1n^{-1/2}(\log n)^a$$</div>
<p>for all sufficiently large integers $n$, and</p>
<div class="math-display">$$\mathbb P_{b+\varepsilon}(|K_o|=\infty)\leq C_2\varepsilon\bigl(\log(1/\varepsilon)\bigr)^a\qquad(0&lt;\varepsilon&lt;\varepsilon_0).$$</div>
<p>In particular $\mathbb P_b(|K_o|=\infty)=0$. When $a=0$ and $b$ is the critical intensity, these are the mean-field upper bounds for the critical cluster tail and supercritical density.</p>
<p><em>Proof.</em> For the first bound take $\varepsilon=n^{-1/2}$, $\beta_1=b-\varepsilon$ and $\beta_2=b$. For large $n$, $\beta_1\geq b/2$, so the comparison gives</p>
<div class="math-display">$$p_n(b)\leq\frac{2+8M/b}{n}\chi(b-n^{-1/2})\leq C_1n^{-1/2}(\log n)^a.$$</div>
<p>This tends to zero, proving nonpercolation at $b$. For the second bound set $\beta_1=b-\varepsilon$ and $\beta_2=b+\varepsilon$, keeping $\varepsilon$ fixed while $n\to\infty$. The events $\{|K_o|\geq n\}$ decrease to $\{|K_o|=\infty\}$, and the term $2\chi(\beta_1)/n$ vanishes. Hence</p>
<div class="math-display">$$\mathbb P_{b+\varepsilon}(|K_o|=\infty)\leq\frac{16M\varepsilon^2}{b-\varepsilon}\chi(b-\varepsilon)\leq\frac{32MC}{b}\varepsilon\bigl(\log(1/\varepsilon)\bigr)^a.$$</div>
<p>This proves the density estimate. The parameter $b$ need not already be identified as a critical point for either argument. Matching lower bounds and optimal logarithmic corrections do not follow from this comparison alone.</p>
<p>The two results supply the cluster-exploration application in the notes, lines 2266–2310, and the upper-bound direction of the mean-field implication discussion. Quantitative susceptibility control is an input to the final corollary; neither stopping the exploration nor entropy comparison proves that input.</p>

## Power-law susceptibility inputs {#section-power-law-input}

<a id="tag-X8T6" data-assertion="corollary" data-title="Tail and density bounds from a power-law susceptibility estimate"></a>
<p>In the countable intensity model of <a href="/tag/JL1S/">JL1S</a>, with uniform weight row bound $M&lt;\infty$, fix $b&gt;0$. Suppose that, for some $C&gt;0$, $0&lt;\gamma&lt;2$, $a\geq0$ and $\varepsilon_0&gt;0$,</p>
<div class="math-display">$$\chi(b-\varepsilon)\leq C\varepsilon^{-\gamma}\bigl(\log(1/\varepsilon)\bigr)^a\qquad(0&lt;\varepsilon&lt;\varepsilon_0),$$</div>
<p>where $\varepsilon_0&lt;\min(e^{-1},b/2)$. Then, as $n\to\infty$ and $\varepsilon\downarrow0$, respectively,</p>
<div class="math-display">$$\mathbb P_b(|K_o|\geq n)=O\!\left(n^{-(2-\gamma)/2}(\log n)^a\right),\qquad
\mathbb P_{b+\varepsilon}(|K_o|=\infty)=O\!\left(\varepsilon^{2-\gamma}(\log(1/\varepsilon))^a\right).$$</div>
<p>In particular $\mathbb P_b(|K_o|=\infty)=0$. The constants may depend on the displayed data; no assertion that $b$ is a critical parameter is needed.</p>
<p><em>Proof.</em> Apply JL1S with $\beta_1=b-n^{-1/2}$ and $\beta_2=b$. For large $n$, $\beta_1\geq b/2$, and both terms in its coefficient are of order $n^{-1}$. The susceptibility bound therefore gives the first estimate. Since $\gamma&lt;2$, its right side tends to zero. For the second estimate fix $\varepsilon$, take $\beta_1=b-\varepsilon$, $\beta_2=b+\varepsilon$, and let the cluster-size threshold tend to infinity in JL1S. Continuity of probability from above gives</p>
<div class="math-display">$$\mathbb P_{b+\varepsilon}(|K_o|=\infty)\leq\frac{16M\varepsilon^2}{b-\varepsilon}\chi(b-\varepsilon).$$</div>
<p>Substitution proves the claim. At $\gamma=1$ this recovers <a href="/tag/QS3L/">QS3L</a>; for the hierarchical application below, the condition $\gamma&lt;2$ determines the range in which the tail and density estimates decay.</p>

## From a critical tail back to susceptibility {#section-reverse-tail}

<a id="tag-1EJP" data-assertion="theorem" data-title="Susceptibility upper bound from a uniform square-root cluster tail"></a>
<p>In the countable intensity model above with uniform weight row bound $M&lt;\infty$, suppose $b&gt;0$ and $C&lt;\infty$ satisfy</p>
<div class="math-display">$$\mathbb P_b(|K_v|\geq n)\leq Cn^{-1/2}\qquad(v\in V,\ n\geq1).$$</div>
<p>There are $c,C'&gt;0$ and an integer $N$ such that, for every vertex $v$, $0&lt;\beta&lt;b$ and $n\geq N$,</p>
<div class="math-display">$$\mathbb P_\beta(|K_v|\geq n)\leq Cn^{-1/2}\exp[-c(b-\beta)\sqrt n],\qquad \chi_v(\beta)\leq\frac{C'}{b-\beta}.$$</div>
<p>Transitivity is one way to obtain the uniform tail hypothesis from a bound at a single root. The theorem does not require susceptibility finiteness below $b$ as an input.</p>
<p><em>Proof.</em> Monotonicity and the tail-sum identity give, for $\beta\leq b$,</p>
<div class="math-display">$$m_n^*(\beta)\leq C\sum_{k=1}^n k^{-1/2}\leq2C\sqrt n.$$</div>
<p>Use the <a href="#/ghost-exploration">cluster-tail differential inequality</a>, and choose $N$ so that $\sqrt n\geq4C/c_0$ for $n\geq N$, where $c_0=1-e^{-1}$. For such $n$ and almost every $\beta\in(0,b)$,</p>
<div class="math-display">$$p_n'(v,\beta)\geq\frac1{2\beta}\left(\frac{c_0\sqrt n}{2C}-1\right)p_n(v,\beta)\geq\frac{c_0}{8bC}\sqrt n\,p_n(v,\beta).$$</div>
<p>Set $c=c_0/(8bC)$. Local Lipschitz regularity permits the integrating-factor argument up to $b$, giving $p_n(v,\beta)\leq e^{-c(b-\beta)\sqrt n}p_n(v,b)$. The assumed tail at $b$ proves the first bound, including when the event probability is zero.</p>
<p>Finally, with $\varepsilon=b-\beta$, sum the tail. The function $x^{-1/2}e^{-c\varepsilon\sqrt x}$ is decreasing and integrable on $(0,\infty)$, so</p>
<div class="math-display">$$\chi_v(\beta)\leq N-1+C\sum_{n\geq N}n^{-1/2}e^{-c\varepsilon\sqrt n}\leq N-1+C\int_0^\infty x^{-1/2}e^{-c\varepsilon\sqrt x}\,dx=N-1+\frac{2C}{c\varepsilon}.$$</div>
<p>Take $C'=b(N-1)+2C/c$. This establishes finiteness and the claimed upper bound simultaneously.</p>
<p>This is the reverse upper-bound implication in the notes' mean-field discussion, lines 2596–2614. Together with the preceding entropy argument it relates susceptibility and critical-tail upper bounds under their explicit hypotheses. The <a href="/tag/9PE0/">four-condition equivalence</a> supplies the matching lower bounds and derivative/second-moment implications under explicit endpoint hypotheses. The <a href="#section-sharp-cutoff">sharper cutoff below</a> uses the resulting susceptibility control.</p>

## The exploration score and second moments {#section-score}

<a id="tag-UTUF" data-assertion="theorem" data-title="Cluster-moment derivative bound from the exploration score"></a>
<p>In the same countable independent-bond model, set $X=|K_o|$, $f_n(\beta)=\mathbb E_\beta[X\wedge n]$ and $s_n(\beta)=\mathbb E_\beta[(X\wedge n)^2]$. For each integer $n\geq1$, $f_n$ is locally Lipschitz on $(0,\infty)$ and</p>
<div class="math-display">$$0\leq f_n'(\beta)\leq\sqrt{\frac M\beta f_n(\beta)s_n(\beta)}\qquad\text{for almost every }\beta&gt;0.$$</div>
<p>If $I\subset(0,\infty)$ is an open interval on which $s(\beta)=\mathbb E_\beta X^2$ is finite, then $\chi_o$ is locally Lipschitz on $I$ and</p>
<div class="math-display">$$0\leq\chi_o'(\beta)\leq\sqrt{\frac M\beta\chi_o(\beta)s(\beta)}\qquad\text{for almost every }\beta\in I.$$</div>
<p>The second-moment assumption is only at the chosen root. Transitivity and finite degree are not required.</p>
<p><em>Proof.</em> First restrict the model to finitely many edges and run the stopped exploration. Its terminal transcript determines $F=X\wedge n$, including when $n=1$ and no edge is queried. Edges of weight zero have deterministic closed answers and can be omitted from the score. For an edge of positive weight $J_e$, the logarithmic derivative of its answer probability is</p>
<div class="math-display">$$\xi_e=\begin{cases}J_e/(e^{\beta J_e}-1),&amp;\text{if open},\\-J_e,&amp;\text{if closed}.\end{cases}$$</div>
<p>Conditional on the answers before a query, the queried coordinate still has its original Bernoulli law. Consequently its score has conditional mean zero and conditional second moment $J_e^2/(e^{\beta J_e}-1)$. Pad the finite exploration by zero increments after it stops, and let $Z$ be the sum of its score increments. Differentiating the finite sum over terminal transcripts gives</p>
<div class="math-display">$$\frac{d}{d\beta}\mathbb E_\beta F=\mathbb E_\beta[FZ],\qquad \mathbb E_\beta Z^2=\sum_e\operatorname{Rev}_\beta(T,e)\frac{J_e^2}{e^{\beta J_e}-1}.$$</div>
<p>The second equality follows from orthogonality of distinct martingale increments, not independence of the randomly selected queried edges. Since $e^u-1\geq u$ for $u\geq0$, the weighted revealment bound yields</p>
<div class="math-display">$$\mathbb E_\beta Z^2\leq\frac1\beta\sum_e J_e\operatorname{Rev}_\beta(T,e)\leq\frac M\beta\mathbb E_\beta F.$$</div>
<p>Cauchy–Schwarz proves the finite-graph inequality; monotonicity gives its lower bound.</p>
<p>For the countable graph, exhaust the edges by increasing finite sets. Finite open-path witnesses show that the restricted $X\wedge n$ increase pointwise to the full $X\wedge n$. Their first and second moments therefore converge to $f_n$ and $s_n$. On a compact interval $[a,b]\subset(0,\infty)$, the finite-graph derivatives are bounded by $\sqrt{M/a}\,n^{3/2}$. The limit $f_n$ is thus Lipschitz there. Integrating the finite inequality over $[u,v]\subset[a,b]$ and applying dominated convergence gives</p>
<div class="math-display">$$0\leq f_n(v)-f_n(u)\leq\int_u^v\sqrt{\frac M\beta f_n(\beta)s_n(\beta)}\,d\beta.$$</div>
<p>The integrand is measurable and locally bounded. Lebesgue differentiation gives the first a.e. derivative bound.</p>
<p>Now take $[a,b]\subset I$. Monotonicity bounds the last integrand, uniformly in $n$ and $\beta\in[a,b]$, by $\sqrt{M\chi_o(b)s(b)/a}&lt;\infty$. Let $n\to\infty$ in the integrated inequality. Monotone convergence of the moments and dominated convergence of the integral give</p>
<div class="math-display">$$0\leq\chi_o(v)-\chi_o(u)\leq\int_u^v\sqrt{\frac M\beta\chi_o(\beta)s(\beta)}\,d\beta.$$</div>
<p>This proves local Lipschitz regularity and the second a.e. bound. At neither limit is convergence of derivatives assumed.</p>

<a id="tag-4GNM" data-assertion="corollary" data-title="Cubic second moments forced by a lower susceptibility derivative bound"></a>
<p>Suppose in addition that the model is invariant and transitive, $0&lt;M&lt;\infty$, and $\chi(\beta)&lt;\infty$ throughout an open interval $I\subset(0,\infty)$. If, for some $c&gt;0$,</p>
<div class="math-display">$$\chi'(\beta)\geq c\chi(\beta)^2\qquad\text{for almost every }\beta\in I,$$</div>
<p>then</p>
<div class="math-display">$$\frac{\beta c^2}{M}\chi(\beta)^3\leq\mathbb E_\beta|K_o|^2\leq\chi(\beta)^3\qquad\text{for almost every }\beta\in I.$$</div>
<p><em>Proof.</em> The <a href="/tag/Y84V/">tree-graph moment bound</a> supplies the upper bound, and in particular finiteness of the second moment throughout $I$. The preceding theorem applies. Square $c\chi^2\leq\sqrt{M\chi s/\beta}$ and divide by $M\chi/\beta$, which is positive since $\chi\geq1$.</p>
<p>Thus on parameter intervals bounded away from zero a fixed lower derivative bound forces the second moment to have the cubic susceptibility scale. The lower derivative bound remains an input; the exploration argument does not establish it.</p>
<p>These results supply the Durrett–Nguyen argument of the notes, lines 2385–2501 (S014), with constant one under the unordered-edge row convention used here. The integrated passage to the limit specifies the regularity and a.e. meaning of the infinite-volume derivative. Finite susceptibility in an invariant transitive model provides the required second moment through the tree-graph bound; identifying that regime with the entire subcritical phase is a separate sharpness result.</p>

## The squared-distance cutoff {#section-sharp-cutoff}

<a id="tag-0O38" data-assertion="theorem" data-title="Exponential cluster-size cutoff from uniform susceptibility control"></a>
<p>In the countable intensity model with uniformly bounded weight rows, suppose $0&lt;a&lt;b&lt;\infty$ and $C&gt;0$ satisfy</p>
<div class="math-display">$$\sup_v\chi_v(\beta)\leq\frac C{b-\beta}\qquad(a&lt;\beta&lt;b).$$</div>
<p>With $c_0=1-e^{-1}$, for every vertex $v$, integer $n\geq1$ and $a&lt;\beta&lt;b$,</p>
<div class="math-display">$$\mathbb P_\beta(|K_v|\geq n)\leq\sqrt{\frac b\beta}\,\mathbb P_b(|K_v|\geq n)\exp\!\left[-\frac{c_0}{4bC}n(b-\beta)^2\right].$$</div>
<p>In particular, a uniform endpoint bound $\mathbb P_b(|K_v|\geq n)\leq Dn^{-1/2}$ retains its square-root prefactor and acquires an exponential cutoff on the scale $(b-\beta)^{-2}$.</p>
<p><em>Proof.</em> Write $p_n(v,s)=\mathbb P_s(|K_v|\geq n)$. The <a href="/tag/JM30/">cluster-tail differential inequality</a> and $m_n^*(s)\leq\sup_v\chi_v(s)\leq C/(b-s)$ give, almost everywhere on $(a,b)$,</p>
<div class="math-display">$$p_n'(v,s)\geq\left[\frac{c_0n(b-s)}{2sC}-\frac1{2s}\right]p_n(v,s)\geq\left[\frac{c_0n(b-s)}{2bC}-\frac1{2s}\right]p_n(v,s).$$</div>
<p>Integrate with an integrating factor from $\beta$ to $b$, using local Lipschitz regularity of $p_n$ at the positive endpoint $b$. The integral of the bracket is</p>
<div class="math-display">$$\frac{c_0n(b-\beta)^2}{4bC}-\frac12\log\frac b\beta.$$</div>
<p>Exponentiation proves the bound, including when $p_n(v,b)=0$. Keeping the negative term in the differential inequality accounts for the factor $\sqrt{b/\beta}$ and avoids imposing a threshold on $n$.</p>
<p>The uniform square-root endpoint hypothesis of <a href="/tag/1EJP/">the reverse-tail theorem</a> already supplies the susceptibility hypothesis, so it also gives this stronger cutoff. Alternatively, in a transitive model the susceptibility hypothesis gives the endpoint square-root upper tail through entropy comparison. This supplies the refinement mentioned in the notes, lines 2609–2614.</p>

## Second moments from the endpoint tail {#section-moment-lower}

<a id="tag-LZCK" data-assertion="theorem" data-title="Cubic second-moment lower bound from mean-field susceptibility and endpoint tails"></a>
<p>In the same countable intensity model, let $b&gt;0$ and fix a root $o$. Suppose there are $C,c&gt;0$ such that, for all sufficiently small $\varepsilon&gt;0$ and all sufficiently large integers $n$,</p>
<div class="math-display">$$\chi_o(b-\varepsilon)\leq C\varepsilon^{-1},\qquad \mathbb P_b(|K_o|\geq n)\geq cn^{-1/2}.$$</div>
<p>Then there is $d&gt;0$ such that</p>
<div class="math-display">$$\mathbb E_{b-\varepsilon}|K_o|^2\geq d\varepsilon^{-3}\geq\frac d{C^3}\chi_o(b-\varepsilon)^3$$</div>
<p>for all sufficiently small $\varepsilon&gt;0$. No transitivity is needed for this implication.</p>
<p><em>Proof.</em> Denote the uniform weight row bound by $M$. Choose $\eta&gt;0$ so small that $2MC\sqrt\eta/(bc)\leq1/4$. For small $\varepsilon$, put $n=\lfloor\eta\varepsilon^{-2}\rfloor$; then $n$ lies in the assumed tail range and</p>
<div class="math-display">$$\frac\eta{2\varepsilon^2}\leq n\leq\frac\eta{\varepsilon^2},\qquad b-\varepsilon\geq\frac b2.$$</div>
<p>Apply the <a href="/tag/JL1S/">entropy comparison</a> between $b-\varepsilon$ and $b$, and write $p_n(s)=\mathbb P_s(|K_o|\geq n)$. Since $p_n(b)\geq c\varepsilon/\sqrt\eta&gt;0$,</p>
<div class="math-display">$$\left(\frac{p_n(b)-p_n(b-\varepsilon)}{p_n(b)}\right)^2\leq\frac{M\varepsilon^2\chi_o(b-\varepsilon)}{(b-\varepsilon)p_n(b)}\leq\frac{2MC\sqrt\eta}{bc}\leq\frac14.$$</div>
<p>Thus $p_n(b-\varepsilon)\geq p_n(b)/2$. On this event the squared cluster size is at least $n^2$, so</p>
<div class="math-display">$$\mathbb E_{b-\varepsilon}|K_o|^2\geq n^2p_n(b-\varepsilon)\geq\frac{c\eta^{3/2}}8\varepsilon^{-3}.$$</div>
<p>Take $d=c\eta^{3/2}/8$. The susceptibility upper bound gives the final comparison.</p>
<p>Under the transitive endpoint hypotheses of <a href="/tag/UPMK/">the susceptibility/critical-tail equivalence</a>, mean-field susceptibility therefore implies a cubic second moment: the equivalence supplies the endpoint lower tail, this theorem supplies the lower moment, and the tree-graph bound supplies the upper moment. The argument chooses a small fixed multiple of the cutoff scale so that entropy comparison preserves a fixed fraction of the endpoint tail. A lower bound on the derivative has not been assumed.</p>

## Summing the tail derivatives {#section-summed-derivative}

<a id="tag-Z9K8" data-assertion="theorem" data-title="Susceptibility derivative lower bound with the second-moment error retained"></a>
<p>Suppose the countable intensity model is invariant and transitive, with finite weight row sum, and $\chi(\beta)&lt;\infty$ on an open interval $I\subset(0,\infty)$. Write $s(\beta)=\mathbb E_\beta|K_o|^2$ and $c_0=1-e^{-1}$. Then</p>
<div class="math-display">$$\chi'(\beta)\geq\frac{c_0}{4\beta\chi(\beta)}\bigl(s(\beta)+\chi(\beta)\bigr)-\frac{\chi(\beta)}{2\beta}\qquad\text{for almost every }\beta\in I.$$</div>
<p><em>Proof.</em> Let $p_n(\beta)=\mathbb P_\beta(|K_o|\geq n)$. Each $p_n$ is increasing and locally Lipschitz. For $[u,v]\subset I$, Tonelli's theorem and the tail-sum identity give</p>
<div class="math-display">$$\int_u^v\sum_{n\geq1}p_n'(\beta)\,d\beta=\sum_{n\geq1}\bigl(p_n(v)-p_n(u)\bigr)=\chi(v)-\chi(u).$$</div>
<p>Here the derivatives are chosen nonnegative on their common full-measure domain; the last equality follows by taking limits of the finite partial sums, since both susceptibilities are finite. Thus the sum is locally integrable and equals $\chi'$ almost everywhere. This justifies differentiating the infinite tail sum.</p>
<p>Transitivity identifies every root's truncated mean, so $m_n^*(\beta)\leq\chi(\beta)$. The <a href="/tag/JM30/">tail derivative inequality</a> therefore gives, simultaneously for every $n$ outside one null set,</p>
<div class="math-display">$$p_n'(\beta)\geq\left(\frac{c_0n}{2\beta\chi(\beta)}-\frac1{2\beta}\right)p_n(\beta).$$</div>
<p>Sum first over $n\leq N$, then let $N\to\infty$. The tree-graph bound makes $s$ finite, and the integer tail identity gives $\sum_{n\geq1}np_n=(s+\chi)/2$. Substitution proves the claim. The negative term is retained throughout; no initial range of cluster sizes is discarded without an estimate.</p>
<p>For example, if $s\geq\kappa\chi^3$ and $\chi\geq4/(c_0\kappa)$, the bound implies $\chi'\geq c_0\kappa\chi^2/(8\beta)$ almost everywhere. This is the precise large-susceptibility form of the second-moment-to-derivative argument in the notes, lines 2578–2597.</p>

## Stopping before a variance overshoot {#section-variance-stop}

<a id="tag-HXNR" data-assertion="proposition" data-title="Maximal martingale bound with truncated predictable variance"></a>
<p>Let $(X_n,\mathcal F_n)_{n\geq0}$ be a real martingale, with $X_0=0$ and $\mathbb E X_n^2&lt;\infty$ for every finite $n$. Write</p>
<div class="math-display">$$Q_0=0,\qquad Q_n=\sum_{i=1}^n\mathbb E[(X_i-X_{i-1})^2\mid\mathcal F_{i-1}].$$</div>
<p>For a stopping time $T\in\mathbb N\cup\{\infty\}$, define $Q_T=\lim_n Q_{n\wedge T}$ and $M_T=\sup_{0\leq n\leq T}|X_n|$. Then for every finite $\lambda\geq0$,</p>
<div class="math-display">$$\mathbb E[M_T^2\mathbf1_{\{Q_T\leq\lambda\}}]\leq4\mathbb E[Q_T\wedge\lambda].$$</div>
<p>The integrand on the left is defined to be zero off the indicated event.</p>
<p><em>Proof.</em> Set $S=\inf\{n\geq0:Q_{n+1}&gt;\lambda\}$, with the infimum of the empty set equal to infinity. Since $Q_{n+1}$ is $\mathcal F_n$-measurable, $S$ is a stopping time. This stops before the increment whose conditional variance would cross the threshold. In particular, $Q_{n\wedge T\wedge S}\leq Q_T\wedge\lambda$.</p>
<p>The martingale $Y_n=X_{n\wedge T\wedge S}$ has increments $(X_i-X_{i-1})\mathbf1_{\{i\leq T\wedge S\}}$. The indicator is $\mathcal F_{i-1}$-measurable, so orthogonality gives</p>
<div class="math-display">$$\mathbb E Y_n^2=\mathbb E Q_{n\wedge T\wedge S}\leq\mathbb E[Q_T\wedge\lambda].$$</div>
<p>The finite-horizon maximal inequality yields $\mathbb E\max_{j\leq n}|Y_j|^2\leq4\mathbb E Y_n^2$. One proof is to stop at the first crossing of a level $t$: the submartingale $|Y_j|$ gives $t\mathbb P(\max_{j\leq n}|Y_j|\geq t)\leq\mathbb E[|Y_n|\mathbf1_{\{\max_{j\leq n}|Y_j|\geq t\}}]$. Integrating in $t$ and applying Cauchy–Schwarz gives the factor four. On $\{Q_T\leq\lambda\}$ no crossing occurs before $T$, so $Y_j=X_{j\wedge T}$. Let $n\to\infty$ by monotone convergence.</p>

## A variance tail controls the damped maximum {#section-variance-tail}

<a id="tag-4GBV" data-assertion="theorem" data-title="Damped martingale maximum from a predictable-variance power tail"></a>
<p>Under the preceding martingale assumptions, suppose $A&gt;0$, $0\leq\theta&lt;1/2$, and $\mathbb P(Q_T\geq x)\leq Ax^{-\theta}$ for every real $x&gt;0$. Then for $h&gt;0$,</p>
<div class="math-display">$$
\mathbb E\left[\frac{M_T}{Q_T}(1-e^{-hQ_T})\mathbf1_{\{0&lt;Q_T&lt;\infty\}}\right]
\leq C_\theta A h^{1/2+\theta},
$$</div>
<p>where</p>
<div class="math-display">$$
C_\theta=\frac{2\,2^{(1-\theta)/2}}{\sqrt{1-\theta}}
\left(\frac1{1-2^{-(1/2+\theta)}}+\frac1{2^{1/2-\theta}-1}\right)
\leq\frac{32}{1-2\theta}.
$$</div>
<p>The integrand is zero when $Q_T$ is zero or infinite; no terminal value $X_\infty$ is needed.</p>
<p><em>Proof.</em> Tail integration gives $\mathbb E[Q_T\wedge b]\leq A b^{1-\theta}/(1-\theta)$. For $k\in\mathbb Z$, let $B_k=\{2^k/h\leq Q_T&lt;2^{k+1}/h\}$. Cauchy–Schwarz and the truncated maximal bound imply</p>
<div class="math-display">$$
\begin{aligned}
\mathbb E[M_T\mathbf1_{B_k}]
&\leq\left(4\mathbb E[Q_T\wedge(2^{k+1}/h)]\,\mathbb P(Q_T\geq2^k/h)\right)^{1/2}\\
&\leq\frac{2A\,2^{(1-\theta)/2}}{\sqrt{1-\theta}}h^{\theta-1/2}2^{(1/2-\theta)k}.
\end{aligned}
$$</div>
<p>On $B_k$, $(1-e^{-hQ_T})/Q_T\leq h\min\{1,2^{-k}\}$. Sum the preceding estimate, using this bound. The terms with $k\geq0$ sum to $(1-2^{-(1/2+\theta)})^{-1}$; those with $k&lt;0$ sum to $(2^{1/2-\theta}-1)^{-1}$. Both series converge for $0\leq\theta&lt;1/2$, and their sum gives $C_\theta$.</p>
<p>For the simpler constant, the prefactor is at most four. The first series is at most $(1-2^{-1/2})^{-1}&lt;4$, and $e^t-1\geq t$ gives</p>
<div class="math-display">$$\frac1{2^{1/2-\theta}-1}\leq\frac{2}{(1-2\theta)\log2}&lt;\frac3{1-2\theta}.$$</div>
<p>Thus $C_\theta&lt;28/(1-2\theta)\leq32/(1-2\theta)$.</p>
<p>These are the martingale mechanisms used in <a href="https://arxiv.org/pdf/2008.11197v2#page=26">Lemmas 3.4–3.5 of the power-law paper</a>. The second proof uses dyadic intervals and gives the stated constant 32 rather than the source's sharper 20. The square-integrability assumptions are explicit here. Applying the bounds to a graph still requires constructing the environment-conditioned exploration, identifying its variance and proving the mass-transport reduction. They do not by themselves establish the improved two-ghost inequality.</p>

## The weighted fluctuation of a cluster {#section-weighted-fluctuation}

<a id="tag-KDN9" data-assertion="theorem" data-title="Environment-conditioned cluster exploration and weighted fluctuation bound"></a>
<p>Let $G=(V,E)$ be a countable simple graph with root $o$. Give its unoriented edges deterministic weights $w(e)\geq0$ such that, for every vertex $v$,</p>
<div class="math-display">$$\sum_{e\ni v}w(e)=1,\qquad\sum_{e\ni v}\sqrt{w(e)}&lt;\infty.$$</div>
<p>Let $p=(p_e)_{e\in E}$ be a random environment with $0&lt;p_e&lt;1$ almost surely. Conditional on $p$, let the edge states $\omega_e$ be independent Bernoulli variables with parameters $p_e$. Write $K$ for the cluster of $o$ and $E(K)$ for the set of edges with at least one endpoint in $K$, counting each edge once. Define $W(K)$ by the nonnegative sum below, allowing infinity, and define $F(K)$ on $\{|K|&lt;\infty\}$:</p>
<div class="math-display">$$
W(K)=\sum_{e\in E(K)}w(e),\qquad
F(K)=\sum_{e\in E(K)}\sqrt{w(e)}\frac{p_e-\omega_e}{\sqrt{p_e(1-p_e)}}.
$$</div>
<p>The second sum converges absolutely almost surely on that event. There is a square-integrable martingale $(Z_n)$, obtained by revealing the environment and then exploring $K$, whose predictable variance satisfies</p>
<div class="math-display">$$Q_\infty=W(K),\qquad |K|/2\leq W(K)\leq|K|,$$</div>
<p>with extended values allowed, and $Z_n\to F(K)$ almost surely when $K$ is finite.</p>
<p>Suppose also that $A&gt;0$, $0\leq\theta&lt;1/2$, and $\mathbb P(|K|\geq n)\leq An^{-\theta}$ for every integer $n\geq1$, under the joint environment and bond law. Then for $h&gt;0$,</p>
<div class="math-display">$$
\mathbb E\left[\frac{|F(K)|}{W(K)}(1-e^{-hW(K)})\mathbf1_{\{|K|&lt;\infty\}}\right]
\leq\frac{32A}{1-2\theta}h^{1/2+\theta}.
$$</div>
<p>All expressions involving $F(K)$ are set to zero off the finite-cluster event. No transitivity or mass-transport assumption is used in this statement.</p>
<p><em>Proof.</em> Enumerate the edges and start with the discovered set $\{o\}$. Query the first unqueried edge incident to a discovered vertex, adding its other endpoint when it is open. If no edge is eligible, make all subsequent increments zero. An eligible edge eventually gets queried: only finitely many edges precede it in the fixed enumeration, and none is queried twice. Induction along each finite open path shows that every vertex of $K$ is eventually discovered. Thus the queried edges are exactly $E(K)$, also when a finite cluster has infinitely many incident edges.</p>
<p>Let $\mathcal F_n$ contain the full environment and the first $n$ queries and answers. Before a query its edge $e$ is known from the past and has not been queried previously. Conditional on the environment and this finite history, its state is still Bernoulli with parameter $p_e$. This follows by fixing a history: its event restricts only the coordinates already queried. Use the increment</p>
<div class="math-display">$$\Delta Z=\sqrt{w(e)}\frac{p_e-\omega_e}{\sqrt{p_e(1-p_e)}}.$$</div>
<p>Its conditional mean is zero and its conditional second moment is $w(e)\leq1$. Therefore $Z_0=0$ and the partial sums form a square-integrable martingale, with $\mathbb E Z_n^2\leq n$. Its predictable variance is the sum of the queried weights. Fairness of the enumeration gives $Q_\infty=W(K)$.</p>
<p>Summing the normalized weight rows over the vertices of $K$ counts internal edges twice and boundary edges once. Tonelli's theorem therefore gives $W(K)\leq|K|\leq2W(K)$, including the infinite case. In particular $W(K)$ is finite exactly when $K$ is finite, and is always positive.</p>
<p>For absolute convergence, put $\xi_e=\sqrt{w(e)}(p_e-\omega_e)/\sqrt{p_e(1-p_e)}$. Conditioning on $p$ gives</p>
<div class="math-display">$$\mathbb E[|\xi_e|\mid p]=2\sqrt{w(e)p_e(1-p_e)}\leq\sqrt{w(e)}.$$</div>
<p>For each deterministic finite vertex set $D$, the sum of these expectations over edges incident to $D$ is finite by the square-root row assumption. Hence the sum of $|\xi_e|$ over those edges is finite almost surely. There are only countably many finite subsets of $V$, so this holds simultaneously for all such $D$, including the random finite set $K$. Every incident edge is eventually queried, giving $Z_n\to F(K)$ there.</p>
<p>Since $Q_\infty\leq|K|$, the assumed integer tail bound implies $\mathbb P(Q_\infty\geq x)\leq Ax^{-\theta}$ for every $x&gt;0$: use the threshold $\lceil x\rceil$ for $x\geq1$, and $A\geq1$ for $x&lt;1$. On finite clusters, $|F(K)|\leq\sup_n|Z_n|$. Apply <a href="/tag/4GBV/">the damped martingale maximum bound</a> with $T=\infty$. Its finite positive variance event is exactly the finite-cluster event, which proves the estimate.</p>
<p>Equivalently, add independent edge marks, independent of both the environment and the bonds, with mark probability $1-e^{-hw(e)}$. Conditional on $K$, the probability that $E(K)$ contains a marked edge is $1-e^{-hW(K)}$. Thus the same bound applies to the expectation of $|F(K)|/W(K)$ restricted to finite clusters touching this edge-ghost field.</p>
<p>This supplies the exploration and variance step in <a href="https://arxiv.org/pdf/2008.11197v2#page=28">the proof of Proposition 3.2</a>. The ratio uses nondegenerate environment probabilities; extending it to probabilities zero or one remains a separate limiting argument. The mass-transport inequality converting two distinct green clusters to this fluctuation, and optimization over invariant weights, are also separate. The stated constant follows from 4GBV and is not the source's sharper constant.</p>

## Optimizing invariant edge weights {#section-invariant-weights}

<a id="tag-G3HT" data-assertion="proposition" data-title="Invariant weighted tests characterize the root-edge square sum"></a>
<p>Let a group $\Gamma$ act transitively by automorphisms on a countable simple graph with at least one edge, and fix a root $o$. Suppose each edge orbit has finite intersection with the set $E_o=\{e:o\in e\}$. Let $a:E\to[0,\infty]$ be $\Gamma$-invariant, and let $B&lt;\infty$ be nonnegative. The following are equivalent:</p>
<div class="math-display">$$\sum_{e\in E_o}a(e)^2\leq B^2;$$</div>
<p>for every nonnegative $\Gamma$-invariant weight $w$ supported on finitely many edge orbits and normalized by $\sum_{e\in E_o}w(e)=1$,</p>
<div class="math-display">$$\sum_{\substack{e\in E_o\\w(e)&gt;0}}\sqrt{w(e)}\,a(e)\leq B.$$</div>
<p>Every such test weight has normalized rows at every vertex and finite square-root row sums. The displayed test omits zero-weight terms, so it is defined even before finiteness of $a$ is known.</p>
<p><em>Proof.</em> Each edge orbit meets $E_o$: move one of the endpoints of any edge to $o$. Write $m_j$ for the positive finite number of edges in this intersection and $a_j$ for their common coefficient. The weight equal to $1/m_j$ on orbit $j$ and zero elsewhere is an admissible test. Its value is $\sqrt{m_j}a_j$, so the test bound first proves that every $a_j$ is finite.</p>
<p>For a nonempty finite set $J$ of orbits put $S_J=\sum_{j\in J}m_ja_j^2$. If $S_J=0$, its desired bound is immediate. Otherwise choose the invariant weight</p>
<div class="math-display">$$w(e)=\frac{a_j^2}{S_J}\quad\text{on orbit }j\in J,\qquad w(e)=0\quad\text{on other orbits}.$$</div>
<p>It is normalized at $o$, and the weighted test becomes</p>
<div class="math-display">$$\sum_{e\in E_o}\sqrt{w(e)}a(e)=\frac{S_J}{\sqrt{S_J}}=\sqrt{S_J}\leq B.$$</div>
<p>There are at most countably many orbits. Exhaust them by finite sets and use monotone convergence to obtain the square-sum bound. Conversely, that bound and Cauchy–Schwarz give every normalized weighted test.</p>
<p>To check admissibility beyond the root, an automorphism carrying $o$ to $v$ maps each orbit's root edges bijectively onto its edges incident to $v$. Thus normalization is the same at every vertex. A finite union of orbits has only finitely many incident edges at each vertex, so its square-root row sum is finite. Normalization also gives $0\leq w(e)\leq1$. Consequently these tests meet the weight assumptions of <a href="/tag/KDN9/">the cluster-fluctuation construction</a>.</p>
<p>A sufficient condition for finite orbit intersections is a positive $\Gamma$-invariant edge function $J$ with $\sum_{e\in E_o}J(e)&lt;\infty$: $J$ is a fixed positive number on each orbit, so infinitely many root edges in one orbit would contradict summability. Finite degree is not required. Zero values of $J$ would not justify this argument on their orbits.</p>
<p>This is the optimization mechanism in <a href="https://arxiv.org/pdf/2008.11197v2#page=22">the proof of Theorem 3.1</a>. Once a probability argument establishes a weighted bound $B_n$ for invariant two-cluster coefficients, the proposition gives their square sum at most $B_n^2$. It does not supply that weighted probability bound, prove mass transport, or remove singularities at environment probabilities zero and one. The normalization uses only finite orbit sets; no infinite square sum is used to define a test weight.</p>

## From two marked clusters to a fluctuation {#section-two-cluster-transport}

<a id="tag-M9TT" data-assertion="theorem" data-title="Two-cluster mass transport for an invariant random environment"></a>
<p>Under the graph, weight and environment assumptions of <a href="/tag/KDN9/">KDN9</a>, suppose a group $\Gamma$ acts transitively on $V$, preserves $w$, and preserves the law of $p$. Assume the vertex mass-transport principle: for every nonnegative diagonally $\Gamma$-invariant function $m:V\times V\to[0,\infty]$,</p>
<div class="math-display">$$\sum_v m(o,v)=\sum_v m(v,o).$$</div>
<p>Independently mark each edge with probability $1-e^{-hw(e)}$, where $h&gt;0$. Call a cluster green if an incident edge is marked. Let $T_e$ be the event that $e$ is closed, its endpoints belong to distinct green clusters, and at least one of those clusters is finite. Then</p>
<div class="math-display">$$
\begin{aligned}
\sum_{e\ni o}\sqrt{w(e)}\,\mathbb E\left[\sqrt{\frac{p_e}{1-p_e}}\mathbf1_{T_e}\right]
&=2\mathbb E\left[\frac{F(K_o)}{|K_o|}\mathbf1_{\{K_o\text{ finite and green}\}}\right]\\
&\leq2\mathbb E\left[\frac{|F(K_o)|}{W(K_o)}\mathbf1_{\{K_o\text{ finite and green}\}}\right].
\end{aligned}
$$</div>
<p>Zero-weight edges are omitted from the sum, and both integrands are zero off the indicated event. In particular, if $\mathbb P(|K_o|\geq n)\leq An^{-\theta}$ for all integers $n\geq1$, with $0\leq\theta&lt;1/2$, the left side is at most $64A h^{1/2+\theta}/(1-2\theta)$.</p>
<p><em>Proof.</em> Put $\xi_e=\sqrt{w(e)}(p_e-\omega_e)/\sqrt{p_e(1-p_e)}$, and let $N_e$ count the distinct finite green clusters touching $e$. First condition on the environment, all bonds except $e$, and the marks. If the endpoints are already connected without $e$, opening it changes neither $N_e$ nor the two-cluster event. Otherwise let $C,D$ be the two endpoint clusters with $e$ deleted. When both are finite, closing $e$ gives $N_e=\mathbf1_{\{C\text{ green}\}}+\mathbf1_{\{D\text{ green}\}}$, while opening it gives $N_e=\mathbf1_{\{C\text{ or }D\text{ green}\}}$. Their difference is one exactly when both are green.</p>
<p>If exactly one of $C,D$ is infinite, the difference is the indicator that the finite one is green; if both are infinite, it is zero. Every infinite cluster of the deleted-edge configuration is green almost surely. Indeed, summing the normalized rows over any infinite vertex set shows that its incident weight is infinite, and independent marks miss it with probability zero. Conditional on the bonds there are only countably many clusters, so this holds simultaneously. Consequently, writing $N_e^0,N_e^1$ for the closed and open values, the difference $N_e^0-N_e^1$ is almost surely the indicator of the endpoint condition defining $T_e$.</p>
<p>Averaging over the remaining Bernoulli variable gives, for $w(e)&gt;0$,</p>
<div class="math-display">$$
\mathbb E[\xi_eN_e]
=\sqrt{w(e)}\,\mathbb E\left[\sqrt{\frac{p_e}{1-p_e}}\mathbf1_{T_e}\right].
$$</div>
<p>This calculation is legitimate without any moment assumption on $p_e/(1-p_e)$: $N_e\leq2$ and $\mathbb E|\xi_e|\leq\sqrt{w(e)}$. The conditional expression on the right equals $\sqrt{w(e)p_e(1-p_e)}(N_e^0-N_e^1)$ before averaging over the environment and the other coordinates, so it is integrable.</p>
<p>For the transport, let $\mathcal C$ be the collection of finite green clusters and set</p>
<div class="math-display">$$
f(u,v)=\sum_{e\ni u}\xi_e
\sum_{\substack{C\in\mathcal C\\e\in E(C)}}\frac{\mathbf1_{\{v\in C\}}}{|C|}.
$$</div>
<p>Its expected absolute outgoing mass is at most $2\sum_{e\ni o}\mathbb E|\xi_e|\leq2\sum_{e\ni o}\sqrt{w(e)}&lt;\infty$. Apply the nonnegative mass-transport principle to the expectations of its positive and negative parts. Invariance follows from the environment law, the invariant weights, and the conditional product laws for bonds and marks. Absolute integrability justifies all rearrangements. The outgoing sum is $\sum_{e\ni o}\xi_eN_e$. In the incoming sum only $K_o$ can contain $o$, and each unoriented edge incident to that cluster occurs once from each endpoint. Thus</p>
<div class="math-display">$$\sum_u f(u,o)=\frac{2F(K_o)}{|K_o|}\mathbf1_{\{K_o\text{ finite and green}\}}.$$</div>
<p>The switching identity now proves the asserted equality. Since $W(K_o)\leq|K_o|$, taking the absolute value of the fluctuation gives the inequality. Finally average over the independent marks and apply KDN9.</p>
<p>This proves the reduction used in <a href="https://arxiv.org/pdf/2008.11197v2#page=23">Lemma 3.3 of the power-law paper</a> by transporting to vertices rather than oriented edges. The hypothesis states the mass-transport property explicitly; transitivity alone is not sufficient. The constant 64 comes from the preceding martingale estimate with constant 32. Conversion from edge marks to cluster-volume events, optimization of the resulting probability bound, and limits at $p_e=0$ or $1$ are separate steps.</p>

## Replacing edge marks by volume thresholds {#section-two-cluster-volume}

<a id="tag-75N0" data-assertion="theorem" data-title="Two-cluster volume bound in a nondegenerate invariant environment"></a>
<p>Retain the countable graph, transitive action, invariant environment and vertex mass-transport assumptions of <a href="/tag/M9TT/">M9TT</a>. Assume $0&lt;p_e&lt;1$ almost surely and $\mathbb P(|K_o|\geq n)\leq An^{-\theta}$ for every integer $n\geq1$, where $A&gt;0$ and $0\leq\theta&lt;1/2$. For an edge $e$, let $S_{e,n}$ be the event that $e$ is closed, its endpoints lie in distinct clusters each having at least $n$ vertices, and at least one of these clusters is finite. Put</p>
<div class="math-display">$$a_n(e)=\mathbb E\left[\sqrt{\frac{p_e}{1-p_e}}\mathbf1_{S_{e,n}}\right].$$</div>
<p>For every nonnegative invariant weight $w$ with normalized vertex rows and finite square-root row sums,</p>
<div class="math-display">$$
\sum_{\substack{e\ni o\\w(e)&gt;0}}\sqrt{w(e)}\,a_n(e)
\leq\frac{C A}{1-2\theta}\,n^{-(1/2+\theta)},
\qquad C=\frac{128}{(1-e^{-1})^2}.
$$</div>
<p>If, in addition, every edge orbit meets the root row in finitely many edges, then</p>
<div class="math-display">$$\sum_{e\ni o}a_n(e)^2\leq\frac{C^2A^2}{(1-2\theta)^2}\,n^{-(1+2\theta)}.$$</div>
<p><em>Proof.</em> Condition on the environment and the bonds. For two distinct clusters $C_1,C_2$, write $W_i$ for the weight of their incident edges and $W_{12}$ for the weight of the union of those edge sets. With $e^{-\infty}=0$, independence of the edge marks gives</p>
<div class="math-display">$$
\begin{aligned}
\mathbb P(C_1,C_2\text{ both green}\mid p,\omega)
&=1-e^{-hW_1}-e^{-hW_2}+e^{-hW_{12}}\\
&\geq(1-e^{-hW_1})(1-e^{-hW_2}).
\end{aligned}
$$</div>
<p>The inequality uses $W_{12}\leq W_1+W_2$. It matters here that the incident edge sets can overlap: their marking events need not be independent. On $S_{e,n}$, normalized rows give $W_i\geq|C_i|/2\geq n/2$, so the conditional probability that both clusters are green is at least $(1-e^{-hn/2})^2$. Hence, by Tonelli and M9TT,</p>
<div class="math-display">$$
(1-e^{-hn/2})^2\sum_{\substack{e\ni o\\w(e)&gt;0}}\sqrt{w(e)}\,a_n(e)
\leq\frac{64A}{1-2\theta}h^{1/2+\theta}.
$$</div>
<p>Take $h=2/n$ and use $2^{1/2+\theta}\leq2$. This proves the weighted estimate, including finiteness of its left side. The coefficients $a_n$ are invariant because the environment law and the conditional bond law are invariant. Under the finite orbit-row assumption, <a href="/tag/G3HT/">G3HT</a> applies to the finite-orbit test weights and gives the square-sum estimate.</p>
<p>This completes the nondegenerate-environment volume and weight-optimization steps in <a href="https://arxiv.org/pdf/2008.11197v2#page=22">Theorem 3.1 of the power-law paper</a>. The explicit constant here is weaker than the source's 200, inherited from the martingale bound above. The finite orbit-row hypothesis is explicit, and is satisfied when the graph carries a strictly positive invariant edge function with a summable root row. Environments with probabilities zero or one still require a separate approximation argument; none is implicit in the displayed ratios.</p>

---
{
  "id": "ghost-fields",
  "title": "Ghost fields and magnetization",
  "subtitle": "Cluster volumes through a Laplace transform",
  "kind": "method",
  "category": "Methods",
  "summary": "Independent vertex marks turn cluster volumes into a smooth positive-field observable. The zero-field value, its right-hand limit and susceptibility have different meanings.",
  "context": ["A countable vertex set and the measurable cluster $K$ of a fixed root, with $T=|K|\\in\\{1,2,\\ldots,\\infty\\}$.", "The percolation law is fixed while the field parameter $h$ varies.", "Vertex marks are independent of each other and of the percolation configuration."],
  "related": ["susceptibility", "binary-tree-percolation", "branching-processes", "russo-formula", "exploration"],
  "sourceIds": ["notes"],
  "aliases": ["ghost", "green vertices", "magnetization", "Laplace transform", "external field"],
  "prototypeUses": []
}
---

## Independent marks {#section-definition}

<a id="tag-VF24" data-assertion="definition" data-title="Ghost field, magnetization and the cluster-volume formula"></a><p>For $h\geq0$, independently mark each vertex green with probability $1-e^{-h}$, and write $\mathcal G_h$ for the marked set. The magnetization is $M(h)=\mathbb P(K\cap\mathcal G_h\ne\varnothing)$. For $h&gt;0$,</p><div class="math-display">$$M(h)=\mathbb E[1-e^{-hT}],$$</div><p>where $e^{-h\infty}=0$. At $h=0$ the marked set is empty almost surely, so $M(0)=0$; no value is assigned to the ambiguous product $0\cdot\infty$.</p><p><em>Proof of the formula.</em> Conditional on a finite cluster of size $t$, all its vertices are unmarked with probability $(e^{-h})^t$. For an infinite cluster, the probability that its first $n$ vertices in a fixed enumeration are all unmarked is $e^{-hn}\to0$. Independence of the marks from the cluster and integration over the cluster law give the identity. Countability also makes the ghost-connection event a countable union of measurable events.</p>

## The zero-field boundary {#section-zero-field}

<a id="tag-8B62" data-assertion="proposition" data-title="Zero-field limit and susceptibility slope"></a><p>With the literal definition $M(0)=0$,</p><div class="math-display">$$\lim_{h\downarrow0}M(h)=\mathbb P(T=\infty),\qquad \lim_{h\downarrow0}\frac{M(h)}h=\mathbb E T,$$</div><p>where the second limit and expectation may be infinite.</p><p><em>Proof.</em> For finite $T$, $1-e^{-hT}\to0$; for infinite $T$ it equals one for every $h&gt;0$. Dominated convergence gives the first limit. For finite $T$,</p><div class="math-display">$$\frac{1-e^{-hT}}h=\int_0^T e^{-ht}\,dt\uparrow T$$</div><p>as $h\downarrow0$; for infinite $T$ the ratio is $1/h\uparrow\infty$. Monotone convergence gives the second limit.</p><p>Thus a positive probability of an infinite cluster produces a jump at the literal zero field. The positive-field limit $M(0+)$ is often used as the zero-field magnetization in statistical mechanics; it is not the probability of hitting an empty ghost field. The <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L567">notes' supercritical binary-tree formula at zero</a> has this limiting interpretation, as recorded in <a href="https://github.com/tomhutchcroft/lrp/issues/238">the source correction</a>.</p>

## Positive-field derivatives {#section-derivatives}

<a id="tag-J2TE" data-assertion="proposition" data-title="Smoothness and derivative formulas at positive field"></a><p>The function $M$ is smooth on $(0,\infty)$, and for every integer $k\geq1$,</p><div class="math-display">$$M^{(k)}(h)=(-1)^{k+1}\mathbb E[T^k e^{-hT};\ T&lt;\infty].$$</div><p>In particular, $M$ is nondecreasing and concave there. The integrands in this formula are defined to be zero when $T=\infty$.</p><p><em>Proof.</em> Fix $h_0&gt;0$. For $h$ in a neighbourhood of $h_0$ bounded below by $h_0/2$, each finite-cluster derivative is bounded in absolute value by $T^k e^{-h_0T/2}$, a bounded function of $T\geq0$. Infinite clusters contribute the constant one to $M(h)$, with derivative zero. Dominated differentiation gives the formula at every order, and its first two signs give the assertions.</p><p>The formula requires no finite cluster moment. It also shows why $\lim_{h\downarrow0}M'(h)$ need not equal the full susceptibility in a percolating regime: infinite clusters contribute to the jump, not to positive-field derivatives. The zero-field ratio in the preceding proposition includes that contribution.</p>

## Tail probabilities and field scale {#section-tails}

<a id="tag-0NVH" data-assertion="proposition" data-title="Discrete tail transform and truncation bounds"></a><p>For $h&gt;0$,</p><div class="math-display">$$M(h)=(1-e^{-h})\sum_{n=1}^{\infty}e^{-h(n-1)}\mathbb P(T\geq n).$$</div><p>For every integer $N\geq1$,</p><div class="math-display">$$(1-e^{-hN})\mathbb P(T\geq N)\leq M(h)\leq h\,\mathbb E[T\wedge N]+\mathbb P(T\geq N).$$</div><p><em>Proof.</em> Sum the geometric series $1-e^{-ht}=(1-e^{-h})\sum_{n=1}^t e^{-h(n-1)}$, also valid at $t=\infty$, and apply Tonelli's theorem. The lower bound restricts the expectation to $\{T\geq N\}$. For the upper bound use $1-e^{-hT}\leq hT$ on $\{T&lt;N\}$ and the bound one on its complement, then enlarge the truncated expectation to $\mathbb E[T\wedge N]$.</p>

<a id="tag-3C2F" data-assertion="proposition" data-title="Equivalence of fractional power tail and magnetization orders"></a><p>Fix $0&lt;\alpha&lt;1$. Then</p><div class="math-display">$$\mathbb P(T\geq n)\asymp n^{-\alpha}\quad(n\to\infty)\qquad\Longleftrightarrow\qquad M(h)\asymp h^\alpha\quad(h\downarrow0).$$</div><p>Here $\asymp$ means two-sided bounds by positive constant multiples, not an exact asymptotic equivalent.</p><p><em>Proof.</em> Suppose first that the tail has these bounds. Enlarge its upper constant to cover all $n\geq1$. Then $\mathbb E[T\wedge N]=\sum_{n=1}^N\mathbb P(T\geq n)\leq C N^{1-\alpha}/(1-\alpha)$. Taking $N=\lceil1/h\rceil$ in the truncation bounds gives both bounds of order $h^\alpha$.</p><p>Conversely, the lower truncation bound with $h=1/n$ gives $\mathbb P(T\geq n)\leq Cn^{-\alpha}$, again enlarged to all $n\geq1$. For a fixed large $L$, the upper truncation bound gives</p><div class="math-display">$$cL^{-\alpha}n^{-\alpha}\leq M\!\left(\frac1{Ln}\right)\leq\frac{C}{(1-\alpha)L}n^{-\alpha}+\mathbb P(T\geq n)$$</div><p>for sufficiently large $n$. Since $\alpha&lt;1$, choose $L$ so that $cL^{-\alpha}&gt;C/((1-\alpha)L)$. Subtraction yields the lower tail bound.</p><p>The restriction $\alpha&lt;1$ matters. A deterministic singleton cluster has $M(h)=1-e^{-h}\sim h$ but no tail at large sizes. An order-$h$ magnetization alone does not imply an order-$n^{-1}$ tail.</p>

## The binary-tree equation {#section-binary-tree}

<a id="tag-4QV6" data-assertion="proposition" data-title="Binary-tree ghost recursion and critical magnetization"></a><p>On the rooted binary tree with two children at every vertex, for $0\leq p\leq1$ and $h&gt;0$,</p><div class="math-display">$$M_p(h)=1-e^{-h}(1-pM_p(h))^2.$$</div><p>At criticality this gives the exact formula</p><div class="math-display">$$M_{1/2}(h)=\frac{2\sqrt{1-e^{-h}}}{1+\sqrt{1-e^{-h}}}\sim2\sqrt h.$$</div><p><em>Proof.</em> The cluster misses all green vertices precisely when the root is unmarked and neither child edge leads to a green vertex in its descendant cluster. These three conditions use independent coordinates, giving the recursion. Put $a=e^{-h}$. At $p=1/2$ the resulting quadratic has one positive root, $2(\sqrt{1-a}-(1-a))/a=2\sqrt{1-a}/(1+\sqrt{1-a})$. The equivalent follows from $1-e^{-h}\sim h$.</p><p>For $p&gt;1/2$, the positive-field limit is the <a href="#/binary-tree-percolation">survival probability</a> $(2p-1)/p^2$, while $M_p(0)=0$ under the literal marking convention. At $h=0$ the recursion alone has multiple solutions and cannot identify the intended convention.</p><p>Source: <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L532">notes, Chapter 2, Ghost fields, lines 532–589</a>. Parameter derivatives of the percolation law require separate Russo-type hypotheses; differentiability in positive field does not supply them.</p>

## Changing the percolation intensity {#section-intensity}

<a id="tag-F7SW" data-assertion="theorem" data-title="Positive-field sprinkling bound and almost-everywhere intensity derivative"></a>
<p>On a nonempty countable vertex set, let symmetric finite nonnegative off-diagonal weights $J$ be preserved by a transitive group, with $L=\sum_{y\ne o}J(o,y)&lt;\infty$. Let $M(\beta,h)$ be the ghost probability for bond probabilities $1-e^{-\beta J(x,y)}$. For $\beta,\varepsilon\geq0$ and $h&gt;0$,</p>
<div class="math-display">$$0\leq M(\beta+\varepsilon,h)-M(\beta,h)\leq\varepsilon L\,M(\beta+\varepsilon,h)\,\partial_h M(\beta,h).$$</div>
<p>For each fixed $h&gt;0$, the function $\beta\mapsto M(\beta,h)$ is Lipschitz with constant $L/(eh)$, and for almost every $\beta&gt;0$,</p>
<div class="math-display">$$0\leq\partial_\beta M(\beta,h)\leq L\,M(\beta,h)\,\partial_h M(\beta,h).$$</div>
<p>Neither finite susceptibility nor almost-sure finiteness of the percolation cluster is assumed.</p>
<p><em>Proof.</em> Couple intensity $\beta+\varepsilon$ as the union of a red intensity-$\beta$ configuration and an independent blue intensity-$\varepsilon$ configuration, using the same independent marks. Every blue probability is at most $\varepsilon J(x,y)$. On an infinite red root cluster there is a green vertex almost surely, so the two ghost indicators agree. Only finite red clusters contribute to their difference.</p>
<p>Condition on the red root cluster being a finite set $S$. The <a href="/tag/BEJT/">last-exit argument</a> bounds the probability that the union reaches a green vertex but the red cluster does not by</p>
<div class="math-display">$$e^{-h|S|}\sum_{x\in S,y\notin S}(1-e^{-\varepsilon J(x,y)})M(\beta+\varepsilon,h)\leq\varepsilon L|S|e^{-h|S|}M(\beta+\varepsilon,h).$$</div>
<p>The last exit must use a blue edge; its state is independent of the remaining path outside $S$. Deleting $S$ can only reduce the latter ghost probability. Average over the countable family of finite $S$ and use <a href="/tag/J2TE/">the positive-field derivative formula</a>, $\partial_hM=\mathbb E[|K_o|e^{-h|K_o|};\ |K_o|&lt;\infty]$. This proves the finite-increment inequality, including the case of infinite red clusters.</p>
<p>Since $t e^{-ht}\leq1/(eh)$ and $M\leq1$, the increment is at most $\varepsilon L/(eh)$. Thus $M(\cdot,h)$ is Lipschitz and hence absolutely continuous and differentiable almost everywhere. At a differentiability point, divide the increment inequality by $\varepsilon$ and let $\varepsilon\downarrow0$; continuity gives the asserted derivative bound.</p>
<p>This supplies an absolutely continuous, almost-everywhere form of the inequality in <a href="https://arxiv.org/pdf/1502.03050v3#page=8">Lemma 1.6 of arXiv:1502.03050v3</a>, together with a finite-increment version. It does not assert differentiability in $\beta$ at every parameter. The field derivative exists at every positive $h$ by J2TE; the two regularity statements are distinct.</p>

## Critical square-root lower bound {#section-critical-lower}

<p>The <a href="/tag/36PN/">integrated-tail argument</a> proves a universal lower bound proportional to $\min\{\sqrt h,1\}$ at a finite critical intensity for countable transitive summable bond models. It retains possible infinite clusters and uses no derivative in the percolation parameter. The saturation is necessary for an all-positive-field statement, because magnetization is at most one.</p>

## Integrating a bounded response {#section-saturated-calculus}

<a id="tag-CVCN" data-assertion="proposition" data-title="Saturated power lower bounds from a scalar differential inequality"></a>
<p>Let $A,r,q&gt;0$, and let $m:(0,\infty)\to[0,1]$ be nondecreasing and locally absolutely continuous. Suppose</p>
<div class="math-display">$$A m(h)^r m'(h)\geq1-m(h)^q$$</div>
<p>for almost every $h&gt;0$. Then, for every $a\in(0,1)$ and every $h&gt;0$,</p>
<div class="math-display">$$m(h)\geq\min\left\{a,\left[\frac{(r+1)(1-a^q)}A h\right]^{1/(r+1)}\right\}.$$</div>
<p>No value at zero, or vanishing right limit there, is assumed.</p>
<p><em>Proof.</em> Fix $h&gt;0$. If $m(h)\geq a$, there is nothing to prove. Otherwise monotonicity gives $m(t)&lt;a$ for $0&lt;t\leq h$. The chain rule for absolutely continuous functions yields</p>
<div class="math-display">$$\frac{d}{dt}m(t)^{r+1}=(r+1)m(t)^r m'(t)\geq\frac{(r+1)(1-a^q)}A$$</div>
<p>almost everywhere on every compact subinterval of $(0,h]$. Integrating from $\varepsilon$ to $h$ and using $m(\varepsilon)^{r+1}\geq0$ gives</p>
<div class="math-display">$$m(h)^{r+1}\geq\frac{(r+1)(1-a^q)}A(h-\varepsilon).$$</div>
<p>Let $\varepsilon\downarrow0$. This proves the second alternative and hence the bound.</p>
<p>For $a=1/2$, the hypotheses $Amm'\geq1-m$ and $Am^2m'\geq2(1-m^2)$ give, respectively,</p>
<div class="math-display">$$m(h)\geq\min\{1/2,\sqrt{h/A}\},\qquad m(h)\geq\min\{1/2,(9h/(2A))^{1/3}\}.$$</div>
<p>These are conditional scalar implications: the second uses the proposition with $r=q=2$ and coefficient $A/2$. Applying either to a model still requires its displayed differential inequality and regularity. In particular, an almost-everywhere intensity derivative such as <a href="/tag/F7SW/">F7SW</a> cannot simply be evaluated at a prescribed critical intensity. The independent <a href="/tag/36PN/">moment-interpolation argument</a> already supplies a percolation field bound without that step. A positive right limit at zero causes no difficulty in the calculus argument, and neither conclusion implies critical nonpercolation.</p>

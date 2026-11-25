---
{
  "id": "integrated-susceptibility",
  "title": "Integrating susceptibility inequalities",
  "subtitle": "Reciprocals, the linear error term, and logarithmic losses",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "Finite-volume pivotal bounds give the upper susceptibility differential inequality and a lower bound at a susceptibility blow-up. An explicit reverse inequality gives the triangle upper bound and logarithmic losses.",
  "context": [
    "The probabilistic bounds use independent bonds with probabilities $1-e^{-\\beta J(u,v)}$ and symmetric nonnegative weights.",
    "The reciprocal triangle bound has its own explicitly stated function and endpoint hypotheses.",
    "Its reverse differential inequality remains an input."
  ],
  "related": [
    "triangle-condition",
    "susceptibility",
    "sharpness"
  ],
  "sourceIds": [
    "notes"
  ],
  "aliases": [
    "integrated triangle bound",
    "reciprocal susceptibility",
    "logarithmic susceptibility bound"
  ],
  "prototypeUses": [
    "triangle-condition"
  ]
}
---

## A finite-volume derivative bound {#section-finite-derivative}

<p>We use the finite BK inequality: under an independent bond law, the probability that two increasing events have disjoint open-edge witnesses is at most the product of their probabilities. The pivotal calculation below is on a finite graph; the passage to infinite volume is made afterwards.</p>
<a id="tag-TAVM" data-assertion="proposition" data-title="Finite-volume susceptibility derivative bound"></a>
<p>Let $F$ be a nonempty finite vertex set with independent edges of probabilities $1-e^{-\beta J(u,v)}$, where $J(u,v)=J(v,u)\geq0$ is finite for $u\neq v$. Write $\tau_F(u,v)$ for connectivity using only vertices of $F$, and set</p>
<div class="math-display">$$\chi_F(u)=\sum_{v\in F}\tau_F(u,v),\qquad M_F=\max_{u\in F}\chi_F(u),\qquad R_F=\max_{u\in F}\sum_{v\in F\setminus\{u\}}J(u,v).$$</div>
<p>For every root $o\in F$ and every $\beta&gt;0$,</p>
<div class="math-display">$$0\leq\chi_F'(o)\leq R_F\chi_F(o)M_F.$$</div>
<p><em>Proof.</em> The finite-coordinate <a href="#/russo-formula">Russo formula</a> gives</p>
<div class="math-display">$$\frac{d}{d\beta}\tau_F(o,x)=\sum_{\{u,v\}\in\binom{F}{2}}J(u,v)\,\mathbb P_\beta\bigl(\{u,v\}\text{ is closed and pivotal for }o\leftrightarrow x\bigr).$$</div>
<p>Indeed, the derivative of an edge probability is $J(u,v)e^{-\beta J(u,v)}$, and pivotality does not depend on that edge's state. If the edge is closed pivotal, its endpoints lie in the distinct clusters of $o$ and $x$, in one of the two possible orders. Paths within those clusters give disjoint witnesses. BK therefore bounds the probability in the sum by</p>
<div class="math-display">$$\tau_F(o,u)\tau_F(v,x)+\tau_F(o,v)\tau_F(u,x).$$</div>
<p>Sum over $x$ and combine the two orientations of each unordered edge:</p>
<div class="math-display">$$\chi_F'(o)\leq\sum_{u\in F}\tau_F(o,u)\sum_{v\in F\setminus\{u\}}J(u,v)\chi_F(v)\leq R_F M_F\chi_F(o).$$</div>
<p>Nonnegativity follows either from the same derivative formula or from monotone coupling. The closed-edge factor in the Russo identity is essential; it has not been replaced by an unconditional pivotal probability with the same coefficient.</p>

## Infinite volume and a susceptibility blow-up {#section-lower-bound}

<a id="tag-MXGM" data-assertion="theorem" data-title="Susceptibility derivative and lower blow-up bound for a transitive intensity model"></a>
<p>Let $V$ be countable, with symmetric nonnegative off-diagonal weights $J(u,v)$ preserved by a transitive group of permutations. Assume</p>
<div class="math-display">$$0&lt;R=\sum_{v\neq o}J(o,v)&lt;\infty.$$</div>
<p>Use independent edges of probabilities $1-e^{-\beta J(u,v)}$, and write $\chi(\beta)=\sum_v\mathbb P_\beta(o\leftrightarrow v)$, which does not depend on $o$. Suppose $0\leq a&lt;b&lt;\infty$ and $\chi(\beta)&lt;\infty$ for every $\beta\in(a,b)$. Then $\chi$ is locally Lipschitz on $(a,b)$ and</p>
<div class="math-display">$$0\leq\chi'(\beta)\leq R\chi(\beta)^2\qquad\text{for almost every }\beta\in(a,b).$$</div>
<p>If additionally $\chi(b)=\infty$, then</p>
<div class="math-display">$$\chi(\beta)\geq\frac1{R(b-\beta)}\qquad(a&lt;\beta&lt;b).$$</div>
<p><em>Proof.</em> Exhaust $V$ by finite sets $F$ containing $o$. Every open connection has a finite path witness, so $\chi_F(o,\beta)\uparrow\chi(\beta)$. The finite-volume row sum is at most $R$, and $\chi_F(v,\beta)\leq\chi(\beta)$ for every $v\in F$, by inclusion in the full cluster and transitivity of the full law. Thus, for $a&lt;s&lt;t&lt;b$, the finite-volume estimate gives</p>
<div class="math-display">$$0\leq\chi_F(o,t)-\chi_F(o,s)\leq R\int_s^t\chi(u)^2\,du.$$</div>
<p>The right side is finite, since $\chi(u)\leq\chi(t)$. Passing to the limit at both endpoints yields the same integral inequality for $\chi$. On each compact subinterval this makes $\chi$ Lipschitz, with constant at most $R$ times the square of its right-endpoint value. Differentiating the integral inequality gives the asserted almost-everywhere bound.</p>
<p>For the endpoint claim, finite-volume continuity and monotonicity give</p>
<div class="math-display">$$\sup_{a&lt;\beta&lt;b}\chi(\beta)=\sup_F\sup_{a&lt;\beta&lt;b}\chi_F(o,\beta)=\sup_F\chi_F(o,b)=\chi(b)=\infty.$$</div>
<p>Hence $\chi(\beta)\to\infty$ as $\beta\uparrow b$. Since $\chi\geq1$, its reciprocal is locally absolutely continuous and satisfies $(1/\chi)'\geq-R$ almost everywhere. Integrating from $\beta$ to $t&lt;b$ gives</p>
<div class="math-display">$$\frac1{\chi(\beta)}\leq\frac1{\chi(t)}+R(t-\beta).$$</div>
<p>Let $t\uparrow b$ and take reciprocals. This proves the lower bound. In particular, no differentiation of an infinite connection sum was used before establishing local regularity.</p>
<p>This is the upper differential inequality and reciprocal argument in the notes, lines 1496–1523. Applying it with $b=\beta_c$ still requires subcritical finiteness, a finite positive critical parameter and $\chi(\beta_c)=\infty$. Those model-specific facts are not consequences of the differential inequality alone. No triangle condition is used in this part.</p>

## The two-cluster derivative identity {#section-two-clusters}

<a id="tag-4800" data-assertion="theorem" data-title="Two-cluster susceptibility derivative identity on a countable group"></a>
<p>Under the hypotheses of the preceding theorem, suppose $V$ is a countable group with identity $o$ and $J(gu,gv)=J(u,v)$ for every $g,u,v$. Let $K_x$ be the full open cluster of $x$. For almost every $\beta\in(a,b)$,</p>
<div class="math-display">$$\begin{aligned}\chi'(\beta)&=\sum_{y\neq o}J(o,y)\,\mathbb E_\beta\!\left[|K_o|\,|K_y|\,\mathbf1_{\{o\not\leftrightarrow y\}}\right]\\&=\sum_{y\neq o}\sum_{z,w}J(o,y)\,\mathbb P_\beta(o\leftrightarrow z,\ y\leftrightarrow w,\ o\not\leftrightarrow y).\end{aligned}$$</div>
<p>These nonnegative sums are finite and bounded by $R\chi(\beta)^2$. The two clusters in the expectation belong to the same percolation configuration; they are not independent.</p>
<p><em>Proof.</em> Before applying BK, the finite-volume pivotal formula gives the exact identity</p>
<div class="math-display">$$\chi_F'(o,\beta)=\sum_{\substack{u,v\in F\\u\neq v}}\sum_{x\in F}J(u,v)\,\mathbb P_\beta(o\leftrightarrow_F u,\ v\leftrightarrow_F x,\ o\not\leftrightarrow_F v).$$</div>
<p>The event on the right says precisely that opening the edge from the root's cluster to the other cluster connects $o$ to $x$. It already forces that edge to be closed, and the oriented sum counts its unique endpoint in the root's cluster.</p>
<p>For each fixed $(u,v,x)$, its indicator converges to the corresponding full-volume indicator as $F$ exhausts $V$. Each connection is witnessed by a finite path. BK bounds the summand, uniformly in $F$, by</p>
<div class="math-display">$$J(u,v)\tau_\beta(o,u)\tau_\beta(v,x).$$</div>
<p>The sum of these bounds is $R\chi(\beta)^2$. Dominated convergence for the countable sum therefore gives $\chi_F'(o,\beta)\to S(\beta)$, where</p>
<div class="math-display">$$S(\beta)=\sum_{u\neq v}\sum_xJ(u,v)\,\mathbb P_\beta(o\leftrightarrow u,\ v\leftrightarrow x,\ o\not\leftrightarrow v).$$</div>
<p>On every compact interval $[s,t]\subset(a,b)$, the derivatives are bounded by $R\chi(t)^2$. Integrating the finite-volume identity and passing to the limit consequently yields $\chi(t)-\chi(s)=\int_s^tS(\beta)\,d\beta$. Thus $\chi'=S$ almost everywhere.</p>
<p>It remains to move the distinguished vertex. In each summand apply the translation by $u^{-1}$, and set $z=u^{-1}$, $y=u^{-1}v$ and $w=u^{-1}x$. This is a bijection between the indexing triples, with $y\neq o$, and invariance gives</p>
<div class="math-display">$$S(\beta)=\sum_{y\neq o}\sum_{z,w}J(o,y)\,\mathbb P_\beta(z\leftrightarrow o,\ y\leftrightarrow w,\ z\not\leftrightarrow y).$$</div>
<p>On $z\leftrightarrow o$, the last condition is equivalent to $o\not\leftrightarrow y$. Tonelli's theorem then turns the sums over $z,w$ into the product of cluster volumes, proving both displayed equalities.</p>
<p>This proves the two-cluster identity in the notes, lines 1532–1547, for translation-invariant models on countable groups. The general unimodular version requires the appropriate mass-transport identity. The next estimate bounds the loss from the independent-cluster value $R\chi^2$ by conditioning on the first cluster; the identity itself does not remove that loss.</p>

## Deleting a revealed cluster {#section-deletion}

<p>At a fixed parameter, write $\tau^S(y,w)$ for the probability of connecting $y$ to $w$ using only vertices of $V\setminus S$, with the same independent edge probabilities as in the full model. Set this quantity to zero if either endpoint belongs to $S$. The next two estimates hold for any independent bond profile on a countable vertex set.</p>
<a id="tag-7902" data-assertion="proposition" data-title="Connection loss on deleting a deterministic vertex set"></a>
<p>For every deterministic $S\subseteq V$ and vertices $y,w$,</p>
<div class="math-display">$$0\leq\tau(y,w)-\tau^S(y,w)\leq\sum_{c\in S}\tau(y,c)\tau(c,w).$$</div>
<p><em>Proof.</em> Couple the deleted and full graphs by retaining the same edges outside $S$. If $y$ and $w$ are connected in the full graph but not in the deleted graph, a simple open path between them visits $S$. Split it at its first such vertex $c$. The two path segments have disjoint edge sets, so BK and a union bound give the upper bound. A segment may be empty when $c$ is an endpoint. On a countable graph the same argument follows by finite-edge exhaustion, since each connection has a finite witness. The lower bound follows from inclusion of the deleted graph.</p>

<a id="tag-J1LW" data-assertion="theorem" data-title="Five-factor bound for the loss of two distinct cluster connections"></a>
<p>Fix $x$ with $K_x$ finite almost surely. For arbitrary $y,z,w$, define</p>
<div class="math-display">$$Q(x,z;y,w)=\mathbb P(x\leftrightarrow z,\ y\leftrightarrow w,\ x\not\leftrightarrow y).$$</div>
<p>Then</p>
<div class="math-display">$$Q(x,z;y,w)=\mathbb E\!\left[\mathbf1_{\{z\in K_x\}}\tau^{K_x}(y,w)\right]$$</div>
<p>and</p>
<div class="math-display">$$0\leq\tau(x,z)\tau(y,w)-Q(x,z;y,w)\leq\sum_{a,c}\tau(x,a)\tau(a,z)\tau(a,c)\tau(y,c)\tau(c,w).$$</div>
<p>The right side is a nonnegative extended sum. Repeated marked vertices are allowed.</p>
<p><em>Proof.</em> For each finite set $S$ containing $x$, the event $K_x=S$ depends only on edges with at least one endpoint in $S$: those within $S$ must connect every vertex to $x$, and all boundary edges must be closed. Edges with both endpoints outside $S$ retain their independent product law conditional on this event whenever it has positive probability. As the finite subsets of a countable set form a countable family and $K_x$ is finite almost surely, summing over $S$ gives the expectation identity.</p>
<p>Subtract this identity from $\mathbb E[\mathbf1_{\{z\in K_x\}}\tau(y,w)]$. The deterministic deletion bound and Tonelli give</p>
<div class="math-display">$$\begin{aligned}0&\leq\tau(x,z)\tau(y,w)-Q(x,z;y,w)\\&\leq\sum_c\mathbb P(x,z,c\text{ lie in one cluster})\,\tau(y,c)\tau(c,w).\end{aligned}$$</div>
<p>The three-point case of the <a href="#/multipoint-trees">tree-graph inequality</a> bounds the cluster probability by $\sum_a\tau(x,a)\tau(a,z)\tau(a,c)$. Substitution proves the five-factor bound. Thus the two BK applications concern paths in a single product law at a time; no disjoint-occurrence claim is made across two independently sampled configurations.</p>

## The weighted open-triangle error {#section-weighted-error}

<a id="tag-4960" data-assertion="corollary" data-title="Susceptibility lower derivative bound with a weighted open-triangle error"></a>
<p>In the countable-group intensity model of the two-cluster identity, define, for $\beta\in(a,b)$,</p>
<div class="math-display">$$\Lambda(\beta)=\sum_{y\neq o}J(o,y)T_\beta^3(o,y).$$</div>
<p>Then $\Lambda(\beta)&lt;\infty$ and, for almost every $\beta\in(a,b)$,</p>
<div class="math-display">$$\chi'(\beta)\geq\bigl(R-\Lambda(\beta)\bigr)\chi(\beta)^2.$$</div>
<p>In particular, if $\sup_{y\neq o}T_\beta^3(o,y)\leq\delta&lt;1$ throughout an interval, then $\chi'(\beta)\geq R(1-\delta)\chi(\beta)^2$ for almost every $\beta$ in that interval.</p>
<p><em>Proof.</em> Finite susceptibility implies that $K_o$ is finite almost surely. Apply the five-factor inequality with $x=o$, multiply by $J(o,y)$, and sum over $y\neq o,z,w$. The two-cluster identity identifies the sum of $J(o,y)Q(o,z;y,w)$ with $\chi'(\beta)$ almost everywhere, while the independent-product term sums to $R\chi(\beta)^2$. The error sums exactly to</p>
<div class="math-display">$$\begin{aligned}&\sum_{y\neq o,z,w,a,c}J(o,y)\tau_\beta(o,a)\tau_\beta(a,z)\tau_\beta(a,c)\tau_\beta(y,c)\tau_\beta(c,w)\\&\qquad=\chi(\beta)^2\sum_{y\neq o}J(o,y)\sum_{a,c}\tau_\beta(o,a)\tau_\beta(a,c)\tau_\beta(c,y)=\chi(\beta)^2\Lambda(\beta).\end{aligned}$$</div>
<p>Here transitivity gives both terminal row sums equal to $\chi(\beta)$, and Tonelli justifies every rearrangement. Also $T_\beta^3(o,y)\leq\chi(\beta)^2$, by bounding its last factor by one and summing the first two, so $\Lambda(\beta)\leq R\chi(\beta)^2&lt;\infty$. All terms being subtracted are therefore finite. Finally $\Lambda\leq R\delta$ under the stated uniform bound.</p>
<p>This supplies a precise five-factor comparison and its weighted summation for the coupling discussion in the notes, lines 1549–1644. The bound involves all weighted neighbours of $o$, including nearby ones. <a href="#/connection-kernels">Open-triangle decay at large separation</a> does not make this weighted error small by itself. The surgery that moves endpoints apart, and its constants, remain to be justified separately.</p>

## The reciprocal estimate {#section-reciprocal}

<a id="tag-TC6Q" data-assertion="theorem" data-title="Integrated quantitative susceptibility bound"></a>
<p>Let $0\leq\beta_0&lt;\beta_c&lt;\infty$. Suppose $\chi:(\beta_0,\beta_c)\to(0,\infty)$ is nondecreasing and locally absolutely continuous, and $D:(\beta_0,\beta_c)\to[1,\infty)$ is measurable and finite-valued. Assume that, for almost every $\beta$ in this interval,</p>
<div class="math-display">$$\chi'(\beta)\geq\frac{\chi(\beta)(\chi(\beta)-D(\beta))}{3\beta^2D(\beta)^2}.$$</div>
<p>Then, for every $\beta\in(\beta_0,\beta_c)$,</p>
<div class="math-display">$$\chi(\beta)\leq\left(1+\frac{\beta_c-\beta}{3\beta\beta_c}\right)\left[\int_\beta^{\beta_c}\frac{ds}{3s^2D(s)^2}\right]^{-1}.$$</div>
<p>The integral in brackets is finite and strictly positive. No limit assumption on $\chi$ at $\beta_c$ is needed for this upper bound.</p>
<p><em>Proof.</em> Set $y=1/\chi$. On each compact subinterval, positivity and continuity bound $\chi$ away from zero, so the reciprocal is absolutely continuous and the chain rule gives</p>
<div class="math-display">$$y'(s)\leq-\frac1{3s^2D(s)^2}+\frac{y(s)}{3s^2D(s)}\quad\text{for almost every }s.$$</div>
<p>Fix $\beta&lt;t&lt;\beta_c$. Since $\chi$ is nondecreasing, $y(s)\leq y(\beta)$ for $s\geq\beta$. Integrating the preceding inequality and using $y(t)\geq0$ therefore gives</p>
<div class="math-display">$$\int_\beta^t\frac{ds}{3s^2D(s)^2}\leq y(\beta)-y(t)+\int_\beta^t\frac{y(s)}{3s^2D(s)}\,ds\leq y(\beta)\left(1+\int_\beta^t\frac{ds}{3s^2D(s)}\right).$$</div>
<p>Let $t\uparrow\beta_c$. Nonnegativity permits monotone convergence in both integrals, and $D\geq1$ gives</p>
<div class="math-display">$$\int_\beta^{\beta_c}\frac{ds}{3s^2D(s)}\leq\frac13\left(\frac1\beta-\frac1{\beta_c}\right).$$</div>
<p>The other integrand is positive everywhere and bounded above by $1/(3\beta^2)$ on an interval of positive finite length. Its integral is therefore strictly positive and finite. Dividing and taking the reciprocal proves the bound.</p>
<p>The linear term in the differential inequality cannot simply be dropped: $\chi(\chi-D)$ is smaller than $\chi^2$. The reciprocal calculation retains that term and accounts for it in the displayed prefactor.</p>

## Bounded and logarithmic diagrams {#section-growth}

<a id="tag-W9IY" data-assertion="corollary" data-title="Susceptibility upper bounds from bounded or logarithmic diagram control"></a>
<p>Under the preceding hypotheses, suppose there are $C&gt;0$, $a\geq0$ and $0&lt;\varepsilon_0&lt;\min(e^{-1},\beta_c-\beta_0)$ such that</p>
<div class="math-display">$$D(\beta_c-u)\leq C\bigl(\log(1/u)\bigr)^a\qquad(0&lt;u&lt;\varepsilon_0).$$</div>
<p>Then there are $C'&gt;0$ and $\varepsilon_1&gt;0$ such that</p>
<div class="math-display">$$\chi(\beta_c-\varepsilon)\leq C'\varepsilon^{-1}\bigl(\log(1/\varepsilon)\bigr)^{2a}\qquad(0&lt;\varepsilon&lt;\varepsilon_1).$$</div>
<p>In particular, a bounded $D$ near $\beta_c$ gives $\chi(\beta_c-\varepsilon)=O(\varepsilon^{-1})$.</p>
<p><em>Proof.</em> Take $\varepsilon$ small enough that the hypotheses apply and $\varepsilon&lt;\min(1/2,\beta_c/2)$. Restrict the reciprocal integral to $s\in[\beta_c-\varepsilon,\beta_c-\varepsilon/2]$. There $s\leq\beta_c$ and</p>
<div class="math-display">$$D(s)\leq C\bigl(\log(2/\varepsilon)\bigr)^a\leq C\,2^a\bigl(\log(1/\varepsilon)\bigr)^a.$$</div>
<p>Consequently,</p>
<div class="math-display">$$\int_{\beta_c-\varepsilon}^{\beta_c}\frac{ds}{3s^2D(s)^2}\geq\frac{\varepsilon}{6\beta_c^2C^2\,2^{2a}(\log(1/\varepsilon))^{2a}}.$$</div>
<p>The prefactor in the integrated bound is bounded as $\varepsilon\downarrow0$, which proves the claimed estimate. Bounded diagrams are the case $a=0$.</p>
<p>A matching lower bound needs separate hypotheses, such as those of the susceptibility blow-up result above. If $D$ is bounded and one also knows $\chi(\beta_c-\varepsilon)\geq c\varepsilon^{-1}$ near the endpoint for some $c&gt;0$, then the two estimates give $\chi(\beta_c-\varepsilon)\asymp\varepsilon^{-1}$. Neither that lower bound nor equality in a logarithmic exponent follows from the upper estimate alone.</p>

## Integrating the corrected quadratic bound {#section-corrected-reciprocal}

<a id="tag-6PGV" data-assertion="theorem" data-title="Integral and logarithmic susceptibility bounds from the corrected quadratic inequality"></a>
<p>Let $0\leq\beta_0&lt;\beta_c&lt;\infty$. Suppose $\chi:(\beta_0,\beta_c)\to(0,\infty)$ is nondecreasing and locally absolutely continuous, and $D:(\beta_0,\beta_c)\to[1,\infty)$ is measurable and finite-valued. If</p>
<div class="math-display">$$\chi'(\beta)\geq\frac{(\chi(\beta)-D(\beta))_+^2}{3\beta^2D(\beta)^2}\qquad\text{for almost every }\beta,$$</div>
<p>then, for every $\beta\in(\beta_0,\beta_c)$,</p>
<div class="math-display">$$\chi(\beta)\leq\left(1+\frac{2(\beta_c-\beta)}{3\beta\beta_c}\right)\left[\int_\beta^{\beta_c}\frac{ds}{3s^2D(s)^2}\right]^{-1}.$$</div>
<p>In particular, if $D(\beta_c-u)\leq C(\log(1/u))^a$ for all sufficiently small $u&gt;0$, with $C&gt;0$ and $a\geq0$, then</p>
<div class="math-display">$$\chi(\beta_c-\varepsilon)=O\!\left(\varepsilon^{-1}(\log(1/\varepsilon))^{2a}\right)\qquad(\varepsilon\downarrow0).$$</div>
<p>No endpoint divergence of $\chi$ is assumed.</p>
<p><em>Proof.</em> Put $y=1/\chi$. The reciprocal is locally absolutely continuous. Since $(1-z)_+^2\geq1-2z$ for every $z\geq0$, the hypothesis gives</p>
<div class="math-display">$$y'(s)\leq-\frac{(1-D(s)y(s))_+^2}{3s^2D(s)^2}\leq-\frac1{3s^2D(s)^2}+\frac{2y(s)}{3s^2D(s)}$$</div>
<p>almost everywhere. Fix $\beta&lt;t&lt;\beta_c$. Monotonicity gives $0&lt;y(s)\leq y(\beta)$ for $s\geq\beta$, so integration yields</p>
<div class="math-display">$$\int_\beta^t\frac{ds}{3s^2D(s)^2}\leq y(\beta)-y(t)+2\int_\beta^t\frac{y(s)}{3s^2D(s)}\,ds\leq y(\beta)\left(1+2\int_\beta^t\frac{ds}{3s^2D(s)}\right).$$</div>
<p>Let $t\uparrow\beta_c$ and use $D\geq1$. The last integral is at most $(1/\beta-1/\beta_c)/3$. The integral on the left is finite and strictly positive, because its integrand is positive and bounded on an interval of positive finite length. Rearrangement proves the first bound.</p>
<p>For the logarithmic consequence, restrict that integral to $s\in[\beta_c-\varepsilon,\beta_c-\varepsilon/2]$. For sufficiently small $\varepsilon$, the denominator there is at most $3\beta_c^2C^2(\log(2/\varepsilon))^{2a}$. Thus the integral is at least a positive constant times $\varepsilon(\log(1/\varepsilon))^{-2a}$, while the prefactor stays bounded.</p>
<p>Taking $D$ to be the triangle diagram applies this calculation to the <a href="/tag/4KBG/">corrected quadratic susceptibility inequality</a>, whenever its hypotheses and the stated regularity hold. The bounded-diagram case gives the susceptibility upper bound of order $(\beta_c-\beta)^{-1}$; a matching lower bound still requires its own endpoint argument. This recovers the logarithmic upper-bound consequence in the <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L2038">notes</a> without using their false stronger numerator. The earlier conditional integral theorem retains its original hypothesis and prefactor.</p>

## Stability under an independent added layer {#section-sprinkling}

<a id="tag-MLLO" data-assertion="theorem" data-title="An independent sparse layer preserves uniformly finite susceptibility"></a>
<p>On a nonempty countable vertex set, let red and blue bonds be mutually independent product configurations with symmetric off-diagonal probabilities $q_0$ and $s$. Write $\chi_0(v)$ for red susceptibility and $\chi(v)$ for susceptibility in their union. Suppose</p>
<div class="math-display">$$M=\sup_v\chi_0(v)&lt;\infty,\qquad\delta=\sup_v\sum_{w\ne v}s(v,w)&lt;\infty,\qquad\delta M&lt;1.$$</div>
<p>Then $\chi(v)\leq\chi_0(v)/(1-\delta M)$ at every vertex. Transitivity is not required.</p>
<p><em>Proof.</em> For ghost intensity $h&gt;0$, write $G_v(h)$ for the union ghost probability and $G^*(h)=\sup_vG_v(h)\leq1$. All red clusters are finite almost surely. The <a href="/tag/BEJT/">independent-layer ghost comparison</a>, together with $1-e^{-hx}\leq hx$, gives</p>
<div class="math-display">$$G_v(h)\leq h\chi_0(v)+\delta\chi_0(v)G^*(h).$$</div>
<p>Taking the supremum and rearranging yields $G^*(h)\leq hM/(1-\delta M)$. Substituting back into the rooted inequality gives $G_v(h)\leq h\chi_0(v)/(1-\delta M)$. Finally $(1-e^{-hT})/h\uparrow T$ as $h\downarrow0$ for any extended nonnegative cluster volume $T$, including $T=\infty$. Monotone convergence proves the susceptibility bound. The rearrangement used only finite ghost probabilities; it did not subtract infinite susceptibilities.</p>

<a id="tag-5LNL" data-assertion="theorem" data-title="Finite susceptibility is right-open and diverges at its finite threshold"></a>
<p>Let a countable independent intensity model be invariant under a transitive group action, with symmetric finite nonnegative off-diagonal weights $J$ and</p>
<div class="math-display">$$0&lt;L=\sum_{y\ne o}J(o,y)&lt;\infty,\qquad q_\beta(x,y)=1-e^{-\beta J(x,y)}.$$</div>
<p>If $\chi_\beta&lt;\infty$ and $0\leq\varepsilon&lt;1/(L\chi_\beta)$, then</p>
<div class="math-display">$$\chi_{\beta+\varepsilon}\leq\frac{\chi_\beta}{1-\varepsilon L\chi_\beta}&lt;\infty.$$</div>
<p>Consequently, if $b_\chi=\sup\{\beta\geq0:\chi_\beta&lt;\infty\}$ is finite, then $b_\chi\geq1/L$, $\chi_{b_\chi}=\infty$, and $\chi_\beta\to\infty$ as $\beta\uparrow b_\chi$.</p>
<p><em>Proof.</em> Add to the intensity-$\beta$ model an independent layer with probabilities $1-e^{-\varepsilon J(x,y)}\leq\varepsilon J(x,y)$. The union has intensity $\beta+\varepsilon$, while its blue row is at most $\varepsilon L$. Apply MLLO with $M=\chi_\beta$. This also proves right-continuity at each finite-susceptibility parameter by monotonicity and squeezing.</p>
<p>The <a href="/tag/E771/">row-sum bound</a>, with diagonal weights taken to be zero, gives finite susceptibility for $\beta L&lt;1$. Thus $b_\chi\geq1/L$. Monotonicity and the definition of the supremum imply finiteness at every $\beta&lt;b_\chi$. If susceptibility were finite at $b_\chi$, the first part would extend finiteness to a larger parameter, a contradiction. Under monotone coupling, each finite path present at a positive parameter is present at some smaller parameter almost surely, since each edge probability is continuous and there are countably many edges. Hence the connection probabilities increase to their endpoint values as $\beta\uparrow b_\chi$. Tonelli over the connected vertices now gives $\chi_\beta\uparrow\chi_{b_\chi}=\infty$.</p>
<p>For the normalized power-law model in <a href="/tag/7F5O/">7F5O</a>, the off-diagonal kernel is summable. If its susceptibility threshold $b_\chi$ is finite, this theorem supplies both endpoint assumptions of that bootstrap at $b=b_\chi$, and hence of the <a href="/tag/26NT/">high-dimensional volume-tail result</a>. The finite-set proof below identifies $b_\chi$ with the percolation threshold. Its finiteness requires a separate model argument, supplied next for kernels containing a lattice plane.</p>

## A finite threshold from planar contours {#section-peierls}

<a id="tag-NUJY" data-assertion="theorem" data-title="Peierls bound and nontriviality of the lattice transition"></a>
<p>For independent nearest-neighbour bonds on $\mathbb Z^2$, suppose each edge is open with probability at least $1-q$. If $0\leq q&lt;1/3$, then</p>
<div class="math-display">$$\mathbb P(|K_0|=\infty)\geq1-\frac{6q}{(1-3q)^2}.$$</div>
<p>In particular, this probability is at least $1/9$ when $q\leq1/12$. Homogeneous nearest-neighbour bond percolation on $\mathbb Z^d$, $d\geq2$, therefore satisfies</p>
<div class="math-display">$$\frac1{2d-1}\leq p_c(\mathbb Z^d)\leq\frac{11}{12}&lt;1.$$</div>
<p><em>Proof.</em> If $K_0$ is finite, let $H$ be the finite set of dual edges crossing its edge boundary. Every corresponding primal edge is closed. At each dual vertex, the degree in $H$ is even: on walking around the corresponding primal face, membership in $K_0$ changes an even number of times. Hence $H$ decomposes into edge-disjoint simple dual cycles.</p>
<p>The positive horizontal ray from zero crosses an odd number of edges of $H$. Indeed, its successive primal vertices start in $K_0$ and eventually stay outside it. Some cycle in the decomposition therefore crosses this ray an odd number of times. The ray avoids dual vertices, so the Jordan curve theorem says that this cycle surrounds zero. This argument also handles boundaries that touch themselves at dual vertices; the whole boundary need not be a simple cycle.</p>
<p>A simple dual cycle of length $n$ surrounding zero has a crossing of the positive ray at $(m+1/2,0)$ with $0\leq m&lt;n$. To see the bound on $m$, the cycle also has a vertex with negative first coordinate, and its coordinate span is at most its length. Encode the cycle by its first crossing along the ray, one of the two orientations of that crossing edge, and the following $n-1$ steps. Each step has at most three choices, since immediate reversal is forbidden. Thus there are at most $2n3^{n-1}\leq2n3^n$ such cycles. Independence bounds the probability that any specified one is closed by $q^n$, even when the bond probabilities differ. A union bound gives</p>
<div class="math-display">$$\mathbb P(|K_0|&lt;\infty)\leq\sum_{n\geq1}2n(3q)^n=\frac{6q}{(1-3q)^2}.$$</div>
<p>At $q=1/12$ the right side is $8/9$. A coordinate plane in $\mathbb Z^d$ gives the same upper bound on $p_c$ for every $d\geq2$.</p>
<p>For the lower bound, a vertex of an infinite cluster in a graph of maximum degree $\Delta\geq2$ starts an open simple path of every finite length. There are at most $\Delta(\Delta-1)^{n-1}$ such paths of length $n$, so their total probability is at most $\Delta p[(\Delta-1)p]^{n-1}$. It tends to zero when $p&lt;1/(\Delta-1)$. Taking $\Delta=2d$ completes the proof.</p>
<p>This proves the nontriviality argument in the <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L160">notes</a>, with an explicit, deliberately crude upper bound. It does not identify the square-lattice threshold or determine behaviour at criticality.</p>

<a id="tag-EBVV" data-assertion="corollary" data-title="Finite susceptibility threshold for summable kernels containing a lattice plane"></a>
<p>Let $d\geq2$ and let $J$ be a symmetric translation-invariant intensity kernel on $\mathbb Z^d$ with finite off-diagonal row sum $L=\sum_{y\ne0}J(y)&gt;0$. Suppose $J(e_1),J(e_2)\geq j&gt;0$. For probabilities $1-e^{-\beta J(y-x)}$, write $\beta_c$ for the infinite-cluster threshold and $b_\chi$ for the susceptibility threshold of <a href="/tag/5LNL/">5LNL</a>. Then</p>
<div class="math-display">$$0&lt;\frac1L\leq b_\chi\leq\beta_c\leq\frac{\log12}{j}&lt;\infty,\qquad\chi_{b_\chi}=\infty.$$</div>
<p><em>Proof.</em> At $\beta=(\log12)/j$, retain only the nearest-neighbour edges of the coordinate plane spanned by $e_1,e_2$. Each retained edge is open with probability at least $11/12$. NUJY gives an infinite cluster at zero with probability at least $1/9$, also in the full model. Thus $\beta_c\leq(\log12)/j$. Whenever the infinite-cluster probability is positive, susceptibility is infinite; monotonicity then gives $b_\chi\leq\beta_c$. The row-sum lower bound and endpoint divergence follow from 5LNL.</p>
<p>For the normalized kernel $J(y)=\|y\|_2^{-d-\alpha}/(d+\alpha)$, $y\ne0$, with $\alpha&gt;0$, the row sum is finite by summing over lattice shells, and one may take $j=1/(d+\alpha)$. Hence $b_\chi\leq(d+\alpha)\log12$. In dimensions $d\geq2$ with $d&gt;3\alpha$, the endpoint hypotheses of <a href="/tag/7F5O/">the cutoff bootstrap</a> are consequently satisfied at $b=b_\chi$; its <a href="/tag/26NT/">volume-tail consequence</a> applies there. Equality $b_\chi=\beta_c$ follows from the finite-set proof below. This plane argument gives no finite-threshold conclusion in dimension one.</p>

## One-dimensional long-range thresholds {#section-one-dimensional}

<a id="tag-65PY" data-assertion="theorem" data-title="A growing-block construction gives a finite threshold below the one-dimensional marginal exponent"></a>
<p>Let $J$ be a symmetric translation-invariant kernel on $\mathbb Z$ with finite off-diagonal row sum $L&gt;0$. Suppose that, for some $c&gt;0$ and $0&lt;\alpha&lt;1$,</p>
<div class="math-display">$$J(r)\geq c|r|^{-1-\alpha}\qquad(r\ne0).$$</div>
<p>Then independent bond percolation with probabilities $1-e^{-\beta J(y-x)}$ has $0&lt;\beta_c&lt;\infty$.</p>
<p><em>Proof.</em> For $n\geq1$, put $N_n=2^{n+1}$, $L_0=M_0=1$, and</p>
<div class="math-display">$$L_n=\prod_{i=1}^nN_i=2^{n(n+3)/2},\qquad M_n=\prod_{i=1}^n(N_i-1).$$</div>
<p>Partition $\mathbb Z$ into aligned intervals of $L_n$ vertices. Each level-$n$ block consists of $N_n$ level-$(n-1)$ blocks. A level-zero block is good, with its singleton as selected connected set. At higher levels, declare a block good when at most one child is bad and every pair of good children's selected sets is joined by an open edge. Select the union of those sets. It is connected inside the block and has at least $M_n$ vertices. All choices and tests use edges with both endpoints in the block.</p>
<p>The selected sets keep a positive fraction of their blocks:</p>
<div class="math-display">$$\frac{M_n}{L_n}=\prod_{i=1}^n(1-N_i^{-1})\geq1-\sum_{i=1}^nN_i^{-1}\geq\frac12.$$</div>
<p>Let $q_n$ be the probability that a level-$n$ block is bad. The child tests are independent, since they use disjoint internal edge sets. Conditional on them and their selected sets, edges between different children remain independent with their original probabilities. For any two good children, the probability of no edge between their selected sets is at most</p>
<div class="math-display">$$\exp\!\left(-\frac{\beta cM_{n-1}^2}{L_n^{1+\alpha}}\right)\leq e^{-\beta A_n},\qquad A_n=\frac{cL_{n-1}^{1-\alpha}}{4N_n^{1+\alpha}}.$$</div>
<p>Indeed, there are at least $M_{n-1}^2$ candidate edges, each of length less than $L_n$. A union bound over pairs of bad children and over unjoined good pairs gives</p>
<div class="math-display">$$q_n\leq N_n^2q_{n-1}^2+N_n^2e^{-\beta A_n},\qquad q_0=0.$$</div>
<p>Since $\alpha&lt;1$, the logarithm of $A_n$ grows quadratically with positive leading coefficient. Thus</p>
<div class="math-display">$$\beta_0=(\log2)\sup_{n\geq1}\frac{4n+11}{A_n}&lt;\infty.$$</div>
<p>For $\beta\geq\beta_0$, induction gives $q_n\leq2^{-2n-8}$. In fact, under the preceding bound on $q_{n-1}$, the two terms in the recursion are at most $2^{-2n-10}$ and $2^{-2n-9}$, respectively. Their sum is smaller than the desired bound.</p>
<p>With probability at least $1-\sum_{n\geq1}2^{-2n-8}&gt;0$, every block containing zero in this nested partition is good. On that event its selected sets are nested, contain zero, and have sizes at least $M_n\to\infty$. They lie in one open cluster, which is therefore infinite. This proves $\beta_c\leq\beta_0$. The row-sum bound gives $\beta_c\geq1/L&gt;0$.</p>
<p>If the lower bound on $J(r)$ holds only for sufficiently large $|r|$, restrict to a sublattice $m\mathbb Z$ with $m$ beyond that cutoff. Its rescaled kernel satisfies the displayed bound at every nonzero integer, with $c$ replaced by $cm^{-1-\alpha}$, so the same conclusion follows. The growing number of children is essential to this construction: discarding a fixed positive fraction at every level would not preserve the density estimate. At $\alpha=1$, $A_n$ no longer grows, so this proof gives no finite threshold at the marginal exponent.</p>

<a id="tag-JK7V" data-assertion="theorem" data-title="Finite total crossing intensity forces one-dimensional clusters to be finite"></a>
<p>For a symmetric translation-invariant intensity kernel on $\mathbb Z$, suppose</p>
<div class="math-display">$$B=\sum_{r\geq1}rJ(r)&lt;\infty.$$</div>
<p>At every finite intensity $\beta\geq0$, all open clusters are finite almost surely. In particular $\beta_c=\infty$.</p>
<p><em>Proof.</em> Let $C_j$ be the event that no open edge crosses the cut between $j$ and $j+1$. Exactly $r$ edges of length $r$ cross this cut. Independence and convergence of the intensity sum give</p>
<div class="math-display">$$\mathbb P_\beta(C_j)=e^{-\beta B}=:p&gt;0.$$</div>
<p>The cuts are dependent, but their covariance is explicit. For $k\geq1$, exactly $(r-k)_+$ edges of length $r$ cross both cuts at zero and at $k$. Set $B_k=\sum_{r&gt;k}(r-k)J(r)$. The total intensity of edges crossing at least one of the two cuts is $2B-B_k$, so</p>
<div class="math-display">$$\operatorname{Cov}(\mathbf1_{C_0},\mathbf1_{C_k})=e^{-2\beta B}\bigl(e^{\beta B_k}-1\bigr)\longrightarrow0.$$</div>
<p>Here $B_k\leq\sum_{r&gt;k}rJ(r)\to0$.</p>
<p>Consequently the variance of $N^{-1}\sum_{j=1}^N\mathbf1_{C_j}$ tends to zero: expand it as the sum of covariances and use their Cesàro convergence to zero. Its mean is $p$. Chebyshev's inequality implies that the probability of no cut in $\{1,\ldots,N\}$ tends to zero. By stationarity the same holds for any fixed shifted interval. Taking a countable union over starting points shows that there are cuts arbitrarily far to the right almost surely. The identical argument applies to the left.</p>
<p>Every vertex is therefore enclosed between two closed cuts. No open path can cross either cut, so its cluster is contained in the finite interval between them. This proves the assertion simultaneously for all vertices.</p>
<p>For $J(r)\asymp |r|^{-1-\alpha}$, the hypothesis holds when $\alpha&gt;1$. Together with 65PY, this proves the non-marginal one-dimensional alternatives in the <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L3897">notes' qualitative phase diagram</a>. The case $\alpha=1$, including finite-threshold existence and discontinuity, remains separate. These arguments do not prove absence of an infinite cluster at criticality when $\alpha&lt;1$.</p>

## The finite-set criterion and sharpness {#section-finite-set}

<p>Let $V$ be countable, with a transitive group preserving symmetric nonnegative off-diagonal intensities $J$, and assume $0&lt;L=\sum_{y\ne o}J(o,y)&lt;\infty$. Write $q_\beta(x,y)=1-e^{-\beta J(x,y)}$. For a finite set $S\ni o$, set</p>
<div class="math-display">$$\varphi_\beta(S)=\sum_{x\in S,\ y\notin S}q_\beta(x,y)\tau_\beta^S(o,x),$$</div>
<p>where $\tau_\beta^S$ uses paths inside $S$. The sum is finite since it is at most $\beta |S|L$. This is the weighted version of the <a href="/tag/6EIM/">finite-set boundary influence</a>.</p>

<p>This bound is the cardinality-numerator consequence of the <a href="https://github.com/tomhutchcroft/lrp/blob/fa3d1bd9b862d919a74c92493e14cbda5c967cf5/wiki/articles/boundary-laws.md#L54">finite-size criterion YLZV</a>. We give an alternative proof using ghost fields.</p>
<p>If $\varphi_\beta(S)&lt;1$, then</p>
<div class="math-display">$$\chi_\beta\leq\frac{|S|}{1-\varphi_\beta(S)}&lt;\infty.$$</div>
<p><em>Proof.</em> Add independent green marks of probability $1-e^{-h}$ at every vertex, and put $G(h)=\mathbb E_\beta[1-e^{-h|K_o|}]\leq1$, with $1-e^{-h\infty}=1$. If $o$ reaches a green vertex outside $S$, take a simple open path to it and split the path at its first exit edge $(x,y)$ from $S$. The internal connection to $x$, the open exit edge and the remaining connection from $y$ to a green vertex have disjoint witnesses, including the mark at the last vertex. BK in the product of bond and mark coordinates, followed by a union bound, gives</p>
<div class="math-display">$$\mathbb P(o\leftrightarrow\mathcal G\setminus S)\leq\sum_{x\in S,y\notin S}\tau_\beta^S(o,x)q_\beta(x,y)G(h)=\varphi_\beta(S)G(h).$$</div>
<p>Transitivity makes the ghost probability at $y$ equal to $G(h)$. Countable BK here follows by finite-coordinate exhaustion of the path and mark witnesses. A green vertex inside $S$ exists with probability $1-e^{-h|S|}$. Thus $G(h)\leq\varphi_\beta(S)G(h)+1-e^{-h|S|}$. Both sides are finite, so rearrangement is legitimate. Divide by $h$ and let $h\downarrow0$; monotone convergence gives the stated bound, including exclusion of an infinite cluster.</p>

<p>The <a href="https://github.com/tomhutchcroft/lrp/blob/fa3d1bd9b862d919a74c92493e14cbda5c967cf5/wiki/articles/finite-size-sharpness.md#L25">wired derivative theorem HATE</a> gives the following inequality. We recall its argument for this application.</p>
<p>For a finite $\Lambda\ni o$, let $f_\Lambda(\beta)=\mathbb P_\beta(o\leftrightarrow V\setminus\Lambda)$. Then for $\beta&gt;0$,</p>
<div class="math-display">$$f_\Lambda'(\beta)\geq\frac{1-f_\Lambda(\beta)}{\beta}\min_{o\in S\subseteq\Lambda}\varphi_\beta(S).$$</div>
<p><em>Proof.</em> Replace the exterior by one vertex $\partial$. Keep the bonds inside $\Lambda$ and give $(x,\partial)$ intensity $\sum_{y\notin\Lambda}J(x,y)$. These finite intensities define a finite product model with exactly the required exit probability: the boundary bond is open when at least one of the original bonds from $x$ to the exterior is open. Distinct boundary bonds use disjoint original coordinates.</p>
<p>In this finite graph, let $\mathscr S$ be the vertices of $\Lambda$ not connected to $\partial$. The event $\mathscr S=S$ says that every edge from $S$ to its complement is closed and that every vertex in $\Lambda\setminus S$ connects to $\partial$ in the complement. It depends on no edge internal to $S$. Consequently the internal edges retain their product law on conditioning on this event.</p>
<p>The intensity form of Russo's formula sums $J(e)$ times the probability that $e$ is closed and pivotal. On $\mathscr S=S$ with $o\in S$, a boundary edge from $x\in S$ is closed pivotal exactly when $o$ connects to $x$ inside $S$. Edges elsewhere cannot be closed pivotal. Therefore</p>
<div class="math-display">$$f_\Lambda'(\beta)=\sum_{o\in S\subseteq\Lambda}\mathbb P_\beta(\mathscr S=S)\sum_{x\in S,y\notin S}J(x,y)\tau_\beta^S(o,x).$$</div>
<p>The terms with $y\notin\Lambda$ are the expanded intensities of the aggregated boundary bonds. In particular, the displayed identity involves no differentiation of an infinite product. Since $\beta J(x,y)\geq q_\beta(x,y)$, the inner sum is at least $\varphi_\beta(S)/\beta$. Finally $\sum_{S\ni o}\mathbb P_\beta(\mathscr S=S)=1-f_\Lambda(\beta)$, proving the inequality.</p>

<p>The following argument recalls the <a href="https://github.com/tomhutchcroft/lrp/blob/fa3d1bd9b862d919a74c92493e14cbda5c967cf5/wiki/articles/finite-size-sharpness.md#L44">sharpness theorem L0TE</a> and <a href="https://github.com/tomhutchcroft/lrp/blob/fa3d1bd9b862d919a74c92493e14cbda5c967cf5/wiki/articles/finite-size-sharpness.md#L65">susceptibility characterization RDF0</a>, supplying the <a href="/tag/DYUM/">weighted sharpness statement</a> in this application. Here is the threshold argument, including the possibility of an infinite threshold. Define</p>
<div class="math-display">$$\widetilde\beta_c=\sup\{\beta\geq0:\varphi_\beta(S)&lt;1\text{ for some finite }S\ni o\}.$$</div>
<p>The certificate set is downward closed because every $\varphi_\beta(S)$ is nondecreasing in $\beta$. It contains $[0,1/L)$ by taking $S=\{o\}$. For every $\beta&lt;\widetilde\beta_c$, a certificate at a larger parameter is also a certificate at $\beta$; the ghost-field certificate bound gives finite susceptibility. Hence $b_\chi,\beta_c\geq\widetilde\beta_c$. If $\widetilde\beta_c=\infty$, all finite parameters have finite susceptibility and both thresholds are infinite.</p>
<p>Otherwise, for $\beta&gt;\widetilde\beta_c$ every finite $S\ni o$ has $\varphi_\beta(S)\geq1$. By the wired derivative inequality, $(\beta f_\Lambda(\beta))'\geq1$ throughout this interval. Integrating from $t\in(\widetilde\beta_c,\beta)$ and using $f_\Lambda(t)\geq0$ gives $f_\Lambda(\beta)\geq1-t/\beta$. Let $t\downarrow\widetilde\beta_c$ and then exhaust $V$ by finite $\Lambda$. The exit events decrease to the event that $K_o$ is infinite, since every finite cluster is contained in some member of the exhaustion. Thus</p>
<div class="math-display">$$\theta(\beta)\geq1-\frac{\widetilde\beta_c}{\beta}\qquad(\beta&gt;\widetilde\beta_c).$$</div>
<p>It follows that $\beta_c\leq\widetilde\beta_c$. Since positive infinite-cluster probability forces infinite susceptibility, $b_\chi\leq\beta_c$ as well. All three thresholds are equal. At a finite threshold, <a href="/tag/5LNL/">right-openness</a> gives $\chi_{\beta_c}=\infty$; the argument does not determine $\theta(\beta_c)$.</p>
<p>At every subcritical parameter, transitivity makes the finite susceptibility uniform. The <a href="/tag/XLWI/">weighted exponential-moment bound</a> then gives exponential cluster-volume tails, for example</p>
<div class="math-display">$$\mathbb P_\beta(|K_o|\geq n)\leq\frac{\sqrt2\chi_\beta}{n}\exp\!\left(-\frac{n}{4\chi_\beta^2}\right)\qquad(n\geq1).$$</div>
<p>The prefactor is retained: a bound $e^{-cn}$ with $c&gt;0$ cannot hold at $n=1$. This completes the notes' <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L950">finite-set and outside-exploration proof</a> in the countable transitive summable setting. For the normalized power-law model, EBVV and 65PY give $b_\chi=\beta_c&lt;\infty$ whenever $d&gt;3\alpha$: use the plane for $d\geq2$, and the growing-block construction for $d=1$, where $\alpha&lt;1/3$. This identifies the parameter in the high-dimensional cutoff and volume-tail conclusions with the percolation threshold in every allowed dimension. No exponential decay in Euclidean distance is claimed for an infinite-range kernel.</p>

## Nearest-neighbour consequences {#section-nearest-consequences}

<a id="tag-IU3W" data-assertion="proposition" data-title="Supercritical lower bound in the homogeneous bond probability"></a>
<p>For homogeneous nearest-neighbour bond percolation on an infinite connected locally finite transitive graph with $p_c&lt;1$,</p>
<div class="math-display">$$\theta(p)\geq\frac{p-p_c}{p(1-p_c)}\qquad(p_c&lt;p\leq1).$$</div>
<p><em>Proof.</em> Write $\varphi_p(S)=p\sum_{x\in S,y\notin S,\,x\sim y}\tau_p^S(o,x)$. The intensity substitution $\beta=-\log(1-p)$ identifies this with the finite-set functional above. Hence $\varphi_p(S)\geq1$ for every finite $S\ni o$ when $p&gt;p_c$.</p>
<p>For the finite-volume exit probability $f_\Lambda(p)$, repeat the wired-boundary calculation recalled above. Now Russo's formula weights a closed-pivotal event by $1/(1-p)$, giving</p>
<div class="math-display">$$f_\Lambda'(p)\geq\frac{1-f_\Lambda(p)}{p(1-p)}\qquad(p_c&lt;p&lt;1).$$</div>
<p>Here only finitely many boundary edges occur, and they may be kept as separate coordinates. Since all those edges can be closed with positive probability, $f_\Lambda(p)&lt;1$. Integrating from $t\in(p_c,p)$ yields</p>
<div class="math-display">$$1-f_\Lambda(p)\leq(1-f_\Lambda(t))\frac{t(1-p)}{p(1-t)}\leq\frac{t(1-p)}{p(1-t)}.$$</div>
<p>Let $t\downarrow p_c$ and exhaust the graph by $\Lambda$. At $p=1$ the graph is connected and infinite, so $\theta(1)=1$.</p>

<a id="tag-468P" data-assertion="proposition" data-title="Lower semicontinuity of the bond threshold under local graph convergence"></a>
<p>Let $(G_n,o_n)$ and $(G,o)$ be infinite connected locally finite transitive graphs. Suppose every fixed-radius rooted ball of $G_n$ is eventually isomorphic to that of $G$. For homogeneous nearest-neighbour bond percolation,</p>
<div class="math-display">$$\liminf_{n\to\infty}p_c(G_n)\geq p_c(G).$$</div>
<p><em>Proof.</em> Fix $0\leq p&lt;p_c(G)$. The finite-set characterization gives a finite $S\ni o$ with $\varphi_p^G(S)&lt;1$. Choose $R$ with $S\subseteq B_R(o)$. A rooted isomorphism on radius $R+1$ transports $S$, every internal edge and every incident boundary edge. It therefore preserves both the restricted connection probabilities and the finite boundary sum: $\varphi_p^{G_n}(S_n)=\varphi_p^G(S)&lt;1$ for all large $n$. The certificate bound gives finite susceptibility on $G_n$, so $p\leq p_c(G_n)$. Let $p\uparrow p_c(G)$.</p>
<p>These are the nearest-neighbour and local-convergence consequences discussed in <a href="https://arxiv.org/pdf/1502.03050v3#page=3">Section 1.2 of arXiv:1502.03050v3</a>. The parameter here is the edge probability $p$, not the unbounded intensity $\beta$. The local argument proves only the displayed lower semicontinuity; it supplies no upper semicontinuity or statement about current locality results.</p>

## Scope of the application {#section-source}

<p>The preliminary notes state the differential inequality in Chapter 5, lines 1688–1701, and give the integrated and logarithmic conclusions at lines 2036–2066. The argument above supplies the calculus passage conditional on the displayed differential inequality and regularity assumptions. For a percolation application, $D$ is the triangle diagram, whose diagonal term is one, but the probabilistic differential inequality and its graph hypotheses must first be established.</p>
<p>The planar comparison above proves finiteness of the critical parameter for its specified kernels. The finite-set argument also establishes sharpness in the stated transitive summable setting. The quantitative triangle theorem remains separate. Local regularity is proved for the transitive intensity model where susceptibility is finite; the reciprocal triangle estimate separately states the analytic regularity it needs. It also does not replace a slowly divergent diagram by a bounded one: the loss of $(\log(1/\varepsilon))^{2a}$ is retained.</p>

<p>A separate <a href="/tag/4KBG/">quadratic triangle bound</a> now supplies a probabilistic lower derivative estimate under mass transport. It suffices for the bounded-triangle susceptibility exponent but has a weaker numerator than the hypothesis of the integrated quantitative estimate above. The two formulas are not interchangeable.</p>

<p>The <a href="/tag/MTYL/">normalized-line counterexample</a> rules out the stronger source formula as a bound valid at every positive subcritical intensity. The conditional calculus statements above remain implications under their displayed hypotheses; they are not evidence that the source formula holds throughout a percolation parameter interval.</p>

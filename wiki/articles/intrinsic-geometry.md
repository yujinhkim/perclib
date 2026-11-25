---
{
  "id": "intrinsic-geometry",
  "title": "Intrinsic balls and cluster-volume tails",
  "subtitle": "Thinning short paths and separating volume from radius",
  "kind": "method",
  "category": "Methods",
  "summary": "A chosen shortest open path compares intrinsic-ball volume with susceptibility at a smaller intensity. An intrinsic-volume bound and a separate one-arm bound together control cluster-volume tails.",
  "context": ["A countable simple graph, with graph distance measured using open edges.", "The thinning comparison uses independent bonds with probabilities $1-e^{-\\beta J_e}$ and finite nonnegative weights.", "The intrinsic one-arm event is not increasing in the edge configuration."],
  "related": ["connectivity", "stopped-exploration", "integrated-lower-tails", "susceptibility"],
  "sourceIds": ["notes"],
  "aliases": ["intrinsic distance", "intrinsic ball", "chemical distance", "intrinsic one-arm", "short-path thinning"],
  "prototypeUses": []
}
---

## Distance inside the open cluster {#section-distance}

<a id="tag-8W1Q" data-assertion="definition" data-title="Intrinsic balls, spheres and one-arm probabilities"></a>
<p>For an edge configuration $\omega$, let $d_\omega(x,y)$ be the smallest number of edges in an open path from $x$ to $y$, with value infinity if there is no such path. For an integer $r\geq0$, define</p>
<div class="math-display">$$B_\omega(x,r)=\{y:d_\omega(x,y)\leq r\},\qquad S_\omega(x,r)=\{y:d_\omega(x,y)=r\}.$$</div>
<p>For a bond law $\mathbb P$ and fixed root $o$, the intrinsic one-arm probability is $Q_r=\mathbb P(S_\omega(o,r)\ne\varnothing)$. In a parameterized independent-bond model on a graph $G$, also define</p>
<div class="math-display">$$Q_r^*(\beta)=\sup_{H\subseteq G}\mathbb P_\beta^H(S_\omega^H(o,r)\ne\varnothing),$$</div>
<p>where $H$ ranges over deterministic subgraphs containing $o$, and the bond law retains the same edge probabilities on $H$.</p>
<p>The ball event $\{x\in B_\omega(o,r)\}$ is increasing, but a sphere need not survive the addition of edges. On the open path $o-u-v$, the sphere of radius two contains $v$; adding the edge $o-v$ makes that sphere empty. Thus an argument about $Q_r$ cannot use stochastic domination as if the arm event were increasing. The supremum over subgraphs supplies a bound for each deleted graph, but an exploration argument must still justify the conditional law on the graph where it restarts.</p>

## Thinning a chosen path {#section-thinning}

<a id="tag-PI11" data-assertion="theorem" data-title="Intrinsic-ball comparison with lower-intensity susceptibility"></a>
<p>Let the edges be independent with probabilities $q_e(t)=1-e^{-tJ_e}$, where each $J_e$ is finite and nonnegative. For $0&lt;\alpha\leq\beta$, every integer $r\geq0$ and every vertex $x$,</p>
<div class="math-display">$$\mathbb P_\beta(x\in B_\omega(o,r))\leq\left(\frac\beta\alpha\right)^r\mathbb P_\alpha(o\leftrightarrow x).$$</div>
<p>Consequently, with possibly infinite expectations,</p>
<div class="math-display">$$\mathbb E_\beta|B_\omega(o,r)|\leq\left(\frac\beta\alpha\right)^r\chi_o(\alpha).$$</div>
<p>If $b&gt;0$ and $\chi_o(b-\varepsilon)\leq C/\varepsilon$ for all sufficiently small $\varepsilon&gt;0$, then for all sufficiently large integers $r$,</p>
<div class="math-display">$$\mathbb E_b|B_\omega(o,r)|\leq\frac{eC}{b}(r+1).$$</div>
<p><em>Proof.</em> Concavity of $t\mapsto1-e^{-tJ_e}$, and its value zero at the origin, give $q_e(\alpha)/q_e(\beta)\geq\alpha/\beta$ whenever $J_e&gt;0$. Sample the configuration at $\beta$. Independently for every edge, retain an open edge with probability $q_e(\alpha)/q_e(\beta)$; edges of zero weight are closed at both parameters. The retained edges are independent with probabilities $q_e(\alpha)$.</p>
<p>On $\{x\in B_\omega(o,r)\}$, choose a shortest open path from $o$ to $x$ using a fixed enumeration to break ties. There are countably many finite paths, so this choice is measurable. A shortest path is simple and has length $\ell\leq r$. Conditional on the entire parameter-$\beta$ configuration, all its edges survive the independent thinning with probability at least $(\alpha/\beta)^\ell\geq(\alpha/\beta)^r$. Survival implies a retained connection from $o$ to $x$. Average this conditional estimate and rearrange. The empty path covers $x=o$, including $r=0$.</p>
<p>Sum over $x$ using Tonelli. For the final assertion take $\beta=b$ and $\alpha=b-b/(r+1)$. For large $r$, the susceptibility hypothesis applies and</p>
<div class="math-display">$$\left(\frac b\alpha\right)^r=\left(1+\frac1r\right)^r\leq e,\qquad \chi_o(\alpha)\leq\frac{C(r+1)}b.$$</div>
<p>This proof uses neither transitivity nor a bound on the vertex degrees. It controls expected intrinsic volume, not the intrinsic arm probability.</p>

## From radius and volume to a cluster tail {#section-tail}

<a id="tag-J1V5" data-assertion="proposition" data-title="Square-root cluster tail from intrinsic volume and arm bounds"></a>
<p>Under any probability law on the countable graph, suppose constants $A,B&lt;\infty$ satisfy</p>
<div class="math-display">$$Q_r\leq\frac A r,\qquad \mathbb E|B_\omega(o,r)|\leq Br\qquad(r\geq1).$$</div>
<p>Then for every integer $n\geq1$,</p>
<div class="math-display">$$\mathbb P(|K_o|\geq n)\leq(A+2B)n^{-1/2}.$$</div>
<p><em>Proof.</em> If $S_\omega(o,r)$ is empty, no vertex of the root cluster can have distance greater than $r$: a shortest path to such a vertex would have a vertex at distance exactly $r$. Thus in this case $K_o=B_\omega(o,r)$. For every $r\geq1$, a union bound and Markov's inequality give</p>
<div class="math-display">$$\mathbb P(|K_o|\geq n)\leq Q_r+\mathbb P(|B_\omega(o,r)|\geq n)\leq\frac A r+\frac{Br}n.$$</div>
<p>Take $r=\lceil\sqrt n\rceil$. Then $1/r\leq n^{-1/2}$ and $r/n\leq2n^{-1/2}$. This proves the claim without any independence or monotonicity assumption on the law.</p>
<p>The arm bound is a separate hypothesis. A linear expected-ball bound alone does not give the conclusion by this argument. A bound on $Q_r^*$ is sufficient, since the original graph is among the subgraphs in its defining supremum.</p>


## Infinite susceptibility forces linear intrinsic volume {#section-lower-volume}

<a id="tag-R5XZ" data-assertion="theorem" data-title="Intrinsic sphere and ball lower bounds at infinite susceptibility"></a>
<p>Let independent bonds on a countable simple graph have probabilities $q(u,v)$ preserved by a transitive group of vertex permutations. Assume</p>
<div class="math-display">$$D=\sum_{v\ne o}q(o,v)&lt;\infty,\qquad \chi_o=\mathbb E|K_o|=\infty.$$</div>
<p>Then, for every integer $r\geq0$,</p>
<div class="math-display">$$\mathbb E|S_\omega(o,r)|\geq1,\qquad r+1\leq\mathbb E|B_\omega(o,r)|\leq\sum_{j=0}^r D^j,$$</div>
<p>where $D^0=1$. In an invariant transitive intensity model with finite weight row $M$, the summability hypothesis holds at every finite intensity $\beta$, since $D\leq\beta M$.</p>
<p><em>Proof.</em> Every vertex at distance at most $r$ has a simple open path of length at most $r$ from the root. A union bound and independence give an upper bound by the sum of the corresponding path weights. Enlarge the sum to all walks and sum their successive endpoints using the row bound $D$. The total weight of walks of length $j$ is at most $D^j$, proving the upper estimate. In particular every finite-radius ball is finite almost surely and has finite mean.</p>
<p>Write $a_m=\mathbb E|S_\omega(o,m)|$ and $b_m=\mathbb E|B_\omega(o,m)|$. For integers $m,n\geq1$ we claim</p>
<div class="math-display">$$b_{m+n}\leq b_m+a_m b_n.$$</div>
<p>To see this, condition on all intrinsic layers through distance $m$. Put $A=B_\omega(o,m-1)$ and $S=S_\omega(o,m)$. The event specifying these layers depends only on edges with at least one endpoint in $A$: it determines reachability at distances below $m$ and the neighbours of the last interior layer. It places no restriction on edges with both endpoints outside $A$. Conditional on any layer configuration of positive probability, those outside edges therefore retain their independent product law.</p>
<p>This conditional statement is valid on the countable graph: the layers are finite almost surely, so there are countably many possible layer configurations. For each fixed choice, the defining event is measurable using only the incident edges of its fixed interior set. Independence of the two coordinate families applies even if that incident set is infinite.</p>
<p>For a vertex at distance between $m+1$ and $m+n$, choose a shortest path from $o$. Its vertex at step $m$ lies in $S$, and its remaining segment never returns to $A$, since every prefix of a shortest path is shortest. Hence, pointwise,</p>
<div class="math-display">$$B_\omega(o,m+n)\subseteq B_\omega(o,m)\ \cup\!\bigcup_{x\in S}B^{G\setminus A}_\omega(x,n).$$</div>
<p>Conditional on the layers, each ball in the union has expected size at most $b_n$: extend the independent law on $G\setminus A$ to the full graph, use monotonicity of the radius-$n$ ball, and then transitivity. Taking expectations proves the claimed renewal inequality. This comparison concerns balls, whose membership events are increasing; it makes no monotonicity assertion about spheres.</p>
<p>If $a_m&lt;1$ for some $m\geq1$, iteration gives</p>
<div class="math-display">$$b_{km}\leq b_m\sum_{j=0}^{k-1}a_m^j\leq\frac{b_m}{1-a_m}\qquad(k\geq1).$$</div>
<p>Every root-cluster vertex has finite intrinsic distance, so monotone convergence as $k\to\infty$ would give $\chi_o&lt;\infty$, a contradiction. Thus $a_m\geq1$ for every $m\geq1$, and $a_0=1$. Summing the disjoint spheres gives $b_r\geq r+1$.</p>
<p>The theorem uses infinite susceptibility rather than the name of a critical parameter. Combined with the preceding thinning comparison and a mean-field susceptibility upper bound below a finite endpoint $b$, it gives $\mathbb E_b|B_\omega(o,r)|\asymp r$ whenever $\chi(b)=\infty$. It still supplies no intrinsic one-arm bound.</p>


## The intrinsic one-arm bootstrap {#section-bootstrap}

<a id="tag-KEO7" data-assertion="theorem" data-title="Intrinsic one-arm bootstrap from an endpoint volume-tail bound"></a>
<p>Consider an invariant transitive independent-bond intensity model on a nonempty countable graph, with finite weight row $M$. Let $0\leq a&lt;b&lt;\infty$, with $b&gt;0$, and suppose $\chi(\beta)&lt;\infty$ for $a&lt;\beta&lt;b$. If for some $\delta&gt;1$ and $C&lt;\infty$,</p>
<div class="math-display">$$\mathbb P_b(|K_o|\geq n)\leq Cn^{-1/\delta}\qquad(n\geq1),$$</div>
<p>then there is $A_0&lt;\infty$ such that</p>
<div class="math-display">$$Q_r^*(b)\leq A_0r^{-1/(\delta-1)}\qquad(r\geq1).$$</div>
<p>In particular, a square-root endpoint volume tail gives an intrinsic one-arm upper bound of order $r^{-1}$. The conclusion is uniform over deterministic subgraphs; it does not assume their intrinsic spheres are increasing events.</p>
<p><em>Proof.</em> Put $\theta=1/(\delta-1)$. We first prove, for $a&lt;\beta&lt;b$ and integers $r,n\geq1$,</p>
<div class="math-display">$$Q_{3r}^*(\beta)\leq Cn^{-1/\delta}+\frac nr\bigl(Q_r^*(\beta)\bigr)^2.$$</div>
<p>Fix a deterministic subgraph $H$ containing $o$ and explore its intrinsic layers. Stop at the first level $j\in\{r,\ldots,2r-1\}$ with $0&lt;|S^H_\omega(o,j)|\leq n/r$, if one exists. If the cluster reaches level $3r$ but has fewer than $n$ vertices, such a level exists: all $r$ middle layers are nonempty, and their total size is less than $n$.</p>
<p>At the stopping level let $A=B^H_\omega(o,j-1)$ and $S=S^H_\omega(o,j)$. As in the renewal proof, conditional on the explored layers, the edges in $H\setminus A$ retain their product law. The stopping rule depends only on those layers, so the same assertion holds at the random stopping level. If the original cluster reaches level $3r$, a shortest path to that level passes through some $x\in S$ and continues in $H\setminus A$. Its endpoint has distance at least $3r-j\geq r$ from $x$ in that remaining graph: a shorter remaining path would contradict its distance $3r$ from $o$. Thus some $x\in S$ has an intrinsic arm of length $r$ in $H\setminus A$.</p>
<p>Transitivity moves each such root $x$ to $o$ while preserving the full model, so its conditional arm probability is at most $Q_r^*(\beta)$. A union bound gives at most $(n/r)Q_r^*(\beta)$ conditional probability of continuation. The stopping event itself implies that the cluster reaches level $r$, and hence has probability at most $Q_r^*(\beta)$. The alternative large-cluster event has probability at most $Cn^{-1/\delta}$: cluster volume is increasing under the coupling from $H$ at $\beta$ to the full graph at $b$. Taking the supremum over $H$ proves the recursion.</p>
<p>For a fixed $\beta\in(a,b)$, set</p>
<div class="math-display">$$A=\max\left\{1,\sup_{r\geq1}r^\theta Q_r^*(\beta)\right\}.$$</div>
<p>This is finite. Indeed, an arm of length $r$ in any subgraph entails at least $r+1$ vertices in its cluster, which is contained in the full cluster under the natural coupling. Finite transitive susceptibility supplies the <a href="/tag/Y84V/">tree-graph moments</a> and hence an <a href="/tag/SNB3/">exponential volume tail</a> at this fixed parameter. Its constants may depend on $\beta$; only finiteness of $A$ is used at this stage.</p>
<p>Write $q=2/(\delta+1)&lt;1$ and, for each $r$, put $t=r^{\delta\theta}A^{-2\delta/(\delta+1)}$. If $t\geq1$, choose the integer $n=\lceil t\rceil\leq2t$ in the recursion. Since $(\delta-1)\theta=1$, both resulting terms have the same scale, giving</p>
<div class="math-display">$$Q_{3r}^*(\beta)\leq(C+2)A^q r^{-\theta}.$$</div>
<p>If $t&lt;1$, then $r^\theta&lt;A^q$, and the same estimate follows from $Q_{3r}^*(\beta)\leq1$. For every $R\geq3$, choose $r=\lfloor R/3\rfloor$. Intrinsic arm events are decreasing in their radius, so $Q_R^*\leq Q_{3r}^*$, and $R/r\leq5$. For $R=1,2$ use $Q_R^*\leq1$. Consequently</p>
<div class="math-display">$$A\leq K A^q,\qquad K=\max\{1,2^\theta,5^\theta(C+2)\}.$$</div>
<p>Since $1\leq A&lt;\infty$, division gives $A\leq K^{1/(1-q)}$, uniformly in $\beta\in(a,b)$.</p>
<p>It remains to pass to $b$; monotonicity of sphere events is not available. Fix $H$ and $r$ and use the increasing uniform coupling as $\beta\uparrow b$. The radius-$r$ ball at $b$ is almost surely finite by the finite-row path bound. Choose a shortest path at $b$ to each vertex in that ball. Only finitely many open edges are used, and each is eventually open at every sufficiently large lower parameter. The radius-$r$ and radius-$(r-1)$ balls therefore eventually agree with their endpoint values. Their difference, the sphere, also agrees. Bounded convergence gives convergence of the arm probability for this fixed $H,r$. The uniform subcritical bound passes to this limit, and then taking the supremum over $H$ proves the theorem.</p>
<p>This supplies the Kozma–Nachmias bootstrap in the notes, lines 2908–2963, under explicit finite-susceptibility and summability hypotheses. The proof handles integer cutoff choices and the endpoint limit separately. It uses monotonicity in the radius, but never monotonicity of intrinsic spheres under edge addition.</p>

## Source scope {#section-source}

<p>These are the definitions, thinning comparison and radius-volume implication in the notes, lines 2804–2907. The renewal argument also supplies the expected-ball lower bound under explicit summability and infinite-susceptibility hypotheses. The one-arm bootstrap is supplied under its separate endpoint-tail and finite-susceptibility hypotheses. A linear expected-ball estimate alone is not used to deduce an arm estimate, and intrinsic distance is not identified with distance in a Euclidean embedding.</p>

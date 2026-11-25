---
{
  "id": "profile-continuity",
  "title": "Continuity in the percolation profile",
  "subtitle": "Finite coordinates, coupling bounds, and an infinite-volume caveat",
  "kind": "method",
  "category": "Methods",
  "summary": "Finite-cylinder expectations vary continuously with the coordinate probabilities. Finite open witnesses give lower semicontinuity in countable products, but full connection probabilities need not be continuous.",
  "context": ["Independent Bernoulli coordinates indexed by $I$, with profile $q\\in[0,1]^I$.", "Profiles carry the product topology: convergence means convergence at each fixed coordinate.", "The finite-coordinate statements require no countability of $I$."],
  "related": ["product-model", "russo-formula", "connectivity", "harris-inequality"],
  "sourceIds": ["perclib-finite-cylinders", "perclib-finite-expectations", "perclib-finite-continuity", "perclib-monotone-coupling", "perclib-product-law"],
  "aliases": ["profile continuity", "cylinder continuity", "lower semicontinuity", "finite expectation", "coupling estimate"],
  "prototypeUses": []
}
---

## The canonical configuration law {#section-product-law}

<p>The <a href="/tag/8NWX/">product law</a> can be written either on binary coordinate functions or on their open sets. The maps $\omega\mapsto\mathbf1_\omega$ and $b\mapsto\{i:b_i=1\}$ are inverse measurable maps, since each coordinate is unchanged. Transporting the product of the one-coordinate laws $q_i\delta_1+(1-q_i)\delta_0$ through this identification gives the same probability measure $\mathbb P_q$ on subsets of $I$. Its total mass is one for every index set.</p>
<p>For a deterministic subset $U\subseteq I$, sample independent probability-$p$ coordinates on $U$ and extend their open set to $I$ with all coordinates outside $U$ closed. The resulting law has profile $q_i=p$ on $U$ and $q_i=0$ outside it: the two laws agree on every finite cylinder and hence on the product sigma-algebra. Taking $U=I$ gives the homogeneous product law. This construction is valid for arbitrary $I$ and $U$; it is a measurable pushforward statement, not an assumption that an uncountable intersection of coordinate events is measurable.</p>

## Restricting the product law {#section-restriction}

<a id="tag-ZNMQ" data-assertion="theorem" data-title="Finite restrictions and weighted expectations on arbitrary coordinate sets"></a>
<p>For any index set $I$, finite $F\subseteq I$, and profile $q\in[0,1]^I$, restriction $\rho_F(\omega)=\omega\cap F$ is measurable and carries $\mathbb P_q$ to the Bernoulli product law with profile $q|_F$. Consequently, for every $\eta\subseteq F$,</p>
<div class="math-display">$$\mathbb P_q(\omega\cap F=\eta)=w_q(\eta),\qquad w_q(\eta)=\prod_{i\in\eta}q_i\prod_{i\in F\setminus\eta}(1-q_i).$$</div>
<p>For every real function $f$ on the subsets of $F$ and every family $\mathcal A\subseteq 2^F$,</p>
<div class="math-display">$$\mathbb E_q[f(\omega\cap F)]=\sum_{\eta\subseteq F}f(\eta)w_q(\eta),\qquad \mathbb P_q(\omega\cap F\in\mathcal A)=\sum_{\eta\in\mathcal A}w_q(\eta).$$</div>
<p>In particular, for disjoint finite $A,B\subseteq I$,</p>
<div class="math-display">$$\mathbb P_q(A\subseteq\omega,\ B\cap\omega=\varnothing)=\prod_{i\in A}q_i\prod_{i\in B}(1-q_i).$$</div>
<p><em>Proof.</em> Each coordinate of the restriction is an original coordinate, so restriction is measurable. The event $\omega\cap F=\eta$ prescribes finitely many independent open and closed coordinates and has the displayed product probability. These events partition the entire space, identifying the restriction law and giving the expectation and event formulas by finite summation. The observable is bounded because its domain is finite, hence integrable. Take $F=A\cup B$ and $\eta=A$ for the mixed cylinder formula.</p>
<p>No countability of $I$ is used. The all-open case $B=\varnothing$ gives $\mathbb P_q(A\subseteq\omega)=\prod_{i\in A}q_i$, including the singleton marginal. If $F=\varnothing$, its only configuration has weight one and the expectation is $f(\varnothing)$. On two coordinates with probabilities $a,b$, the configuration with only the first open has mass $a(1-b)$. At $(a,b)=(1,0)$ the whole law is concentrated on that configuration. These endpoint cases use the same formula, without division by a coordinate probability.</p>

## Finite observations {#section-finite}

<a id="tag-RA0Z" data-assertion="theorem" data-title="Finite-cylinder expectations are continuous in the ambient profile"></a><p>Let $F\subseteq I$ be finite and let $f:\{0,1\}^F\to\mathbb R$. Then</p><div class="math-display">$$q\longmapsto\mathbb E_q[f(\omega|_F)]$$</div><p>is continuous on $[0,1]^I$, including profiles with zero or one coordinates. In particular, pointwise convergence of profiles implies convergence of every fixed finite-cylinder probability. For bond percolation, connection probabilities inside a fixed finite vertex domain have this property.</p><p><em>Proof.</em> Restriction to $F$ has the independent Bernoulli law with profile $q|_F$. Its expectation is the <a href="/tag/7WIO/">finite configuration polynomial</a></p><div class="math-display">$$\sum_{\eta\subseteq F} f(\eta)\prod_{i\in\eta}q_i\prod_{i\in F\setminus\eta}(1-q_i).$$</div><p>It is continuous in its finitely many arguments, and restriction $q\mapsto q|_F$ is continuous for the product topology. A connection inside a finite vertex domain uses only its finitely many internal pairs, so it is a cylinder event. An empty coordinate block gives a constant expectation.</p>

## A quantitative comparison {#section-coupling}

<a id="tag-RGN6" data-assertion="proposition" data-title="Finite-block profile perturbation bound"></a><p>For the same $F$ and $f$, put $\operatorname{osc}(f)=\max f-\min f$. For any two profiles $q,r$,</p><div class="math-display">$$\left|\mathbb E_q f(\omega|_F)-\mathbb E_r f(\omega|_F)\right|\leq\operatorname{osc}(f)\min\!\left\{1,\sum_{i\in F}|q_i-r_i|\right\}.$$</div><p>For an event depending only on $F$, its probability difference is therefore at most $\min\{1,\sum_{i\in F}|q_i-r_i|\}$.</p><p><em>Proof.</em> Use independent uniform variables $U_i$, $i\in F$, and set $X_i=\mathbf1_{\{U_i\leq q_i\}}$ and $Y_i=\mathbf1_{\{U_i\leq r_i\}}$. Coordinate $i$ disagrees with probability $|q_i-r_i|$. A union bound gives $\mathbb P(X\neq Y)\leq\min\{1,\sum_i|q_i-r_i|\}$. Since $|f(X)-f(Y)|\leq\operatorname{osc}(f)\mathbf1_{\{X\neq Y\}}$, taking expectations proves the bound. No coordinatewise ordering of $q$ and $r$ is required.</p>

## Ordered profiles {#section-order}

<a id="tag-6B9V" data-assertion="theorem" data-title="Ordered product coupling and comparison of nonnegative observables"></a>
<p>Suppose $I$ is countable and $p_i\leq q_i$ for every $i\in I$. There is a probability law $\gamma$ on $2^I\times2^I$ whose marginals are $\mathbb P_p$ and $\mathbb P_q$ and for which $\omega\subseteq\omega'$ almost surely. Hence every increasing measurable event $A$ and every increasing measurable $H:2^I\to[0,\infty]$ satisfy</p>
<div class="math-display">$$\mathbb P_p(A)\leq\mathbb P_q(A),\qquad \mathbb E_p[H]\leq\mathbb E_q[H].$$</div>
<p>The expectations are extended nonnegative integrals; neither is assumed finite. For a countable vertex set, the same construction couples bond configurations on all unordered pairs, including diagonal coordinates, provided the profiles are ordered on all those pairs.</p>
<p><em>Proof.</em> Independently at each coordinate $i$, choose the pair of bits $(X_i,Y_i)$ with probabilities</p>
<div class="math-display">$$\mathbb P((X_i,Y_i)=(1,1))=p_i,\quad \mathbb P((X_i,Y_i)=(0,1))=q_i-p_i,\quad \mathbb P((X_i,Y_i)=(0,0))=1-q_i.$$</div>
<p>These numbers are nonnegative and sum to one. The remaining pair $(1,0)$ is never chosen. The map from the product of these three-state spaces to the two open-coordinate sets is measurable, since its coordinates are measurable. Its pushforward has the required marginals: each first bit has parameter $p_i$, each second bit has parameter $q_i$, and finite families of either kind remain independent. Cylinder uniqueness identifies both product laws.</p>
<p>Every configuration in the three-state construction satisfies $X_i\leq Y_i$ for all $i$. On the target pair space, the event $\omega\subseteq\omega'$ is measurable because it is the countable intersection of the events excluding an open first bit and a closed second bit. Thus it has $\gamma$-probability one. Increasingness gives $\mathbf1_A(\omega)\leq\mathbf1_A(\omega')$ and $H(\omega)\leq H(\omega')$ on this event. Integrate and use the marginal identities. Monotonicity of the nonnegative integral applies even when an expectation is infinite.</p>
<p>The construction includes $p_i=0$, $q_i=1$, empty coordinate sets and equal profiles. If $p=q$, the middle state has zero probability at each coordinate, so countability gives $\omega=\omega'$ almost surely. At the extreme profiles $p\equiv0$, $q\equiv1$, the pair is the empty and full configuration. No division by $p_i$ or $1-q_i$ occurs.</p>
<p>This comparison concerns ordered profiles. The finite-block perturbation bound above also compares profiles that are not ordered. Neither result asserts continuity for a general infinite-volume event.</p>

## Finite witnesses in infinite volume {#section-witnesses}

<a id="tag-ARYU" data-assertion="proposition" data-title="Finite open witnesses give lower semicontinuous probabilities"></a><p>Suppose $I$ is countable and an event $A$ has a representation</p><div class="math-display">$$A=\bigcup_{F\in\mathcal W}\{\omega:F\subseteq\omega\},$$</div><p>where every $F\in\mathcal W$ is finite. Then $A$ is measurable and $q\mapsto\mathbb P_q(A)$ is lower semicontinuous in the product topology. Thus, whenever $q^{(n)}\to q$ coordinatewise,</p><div class="math-display">$$\mathbb P_q(A)\leq\liminf_{n\to\infty}\mathbb P_{q^{(n)}}(A).$$</div><p>This applies to connection events on any countable graph.</p><p><em>Proof.</em> There are countably many finite subsets of $I$. Enumerate the witness family and let $A_m$ be the union of its first $m$ cylinder events (with the empty-family case immediate). Then $A_m\uparrow A$, each $A_m$ depends on finitely many coordinates, and</p><div class="math-display">$$\mathbb P_q(A)=\sup_m\mathbb P_q(A_m).$$</div><p>Every function in this supremum is continuous by the finite-cylinder result, so their supremum is lower semicontinuous. A connection has a finite open path witness, giving the stated application.</p>

<p>Continuity can fail even for a connection between two fixed vertices. Take the graph with vertices $x,y,v_1,v_2,\ldots$ and edges $\{x,v_n\},\{v_n,y\}$ for every $n$. In profile $q^{(n)}$, give the two edges through $v_n$ probability one and every other edge probability zero. Each fixed edge probability tends to zero, but $\mathbb P_{q^{(n)}}(x\leftrightarrow y)=1$ for all $n$, whereas the all-zero limiting profile gives probability zero. This agrees with lower semicontinuity and rules out an unrestricted continuity claim.</p><p>Nor does this argument apply directly to the event of an infinite cluster: no finite open set certifies that event. Continuity of an infinite-cluster probability, including behavior at criticality, needs additional information.</p>

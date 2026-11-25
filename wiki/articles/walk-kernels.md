---
{
  "id": "walk-kernels",
  "title": "Walk kernels and intensity bounds",
  "subtitle": "Nonnegative sums before their percolation application",
  "kind": "method",
  "category": "Foundations",
  "summary": "Uniform row sums control the total weight of vertex sequences for arbitrary nonnegative kernels. Removing the diagonal gives the percolation application, including finite intensities with nonzero diagonal weights.",
  "context": ["An arbitrary vertex set $V$ and a kernel $a:V\\times V\\to[0,\\infty]$ for the deterministic statements.", "Nonnegative sums mean suprema of finite subsums; products use $0\\cdot\\infty=0$ and the empty product is one.", "The probability applications assume countable $V$ and independent unordered-pair coordinates. Intensities and their parameter are finite; thresholds may be infinite."],
  "related": ["subcritical-bound", "product-symmetries", "susceptibility", "criticality", "bounded-degree-paths"],
  "sourceIds": ["perclib-walk-sums", "perclib-row-sum", "perclib-intensity-definitions", "perclib-intensity-bounds", "perclib-finite-graphs"],
  "aliases": ["walk kernel", "nonnegative matrix", "geometric row bound", "off-diagonal mask", "zero intensity row"],
  "prototypeUses": []
}
---

## Sequence weights {#section-weights}

<a id="tag-O357" data-assertion="definition" data-title="Nonnegative sequence weights, walk sums and diagonal removal"></a>
<p>For a root $v_0=v$ and a sequence $(v_1,\ldots,v_n)\in V^n$, its weight is</p>
<div class="math-display">$$w_a(v;v_1,\ldots,v_n)=\prod_{i=1}^n a(v_{i-1},v_i),\qquad W_n^a(v)=\sum_{(v_1,\ldots,v_n)\in V^n}w_a(v;v_1,\ldots,v_n).$$</div>
<p>The unique empty sequence has weight one, so $W_0^a(v)=1$. Sequences may repeat vertices or edges, and diagonal entries may be nonzero. Define the diagonal-removed kernel by $a^\circ(v,w)=a(v,w)$ when $v\ne w$, and $a^\circ(v,v)=0$.</p>
<p>These are deterministic weights. Even when the entries of $a$ are bond probabilities, the product along a sequence with repeated edges is not generally the probability that its edges are open.</p>

## The row estimate {#section-row-estimate}

<a id="tag-HDHT" data-assertion="theorem" data-title="Extended nonnegative walk sums satisfy the geometric row bound"></a>
<p>For every nonnegative extended kernel,</p>
<div class="math-display">$$W_{n+1}^a(v)=\sum_{u\in V}a(v,u)W_n^a(u).$$</div>
<p>If $\sum_u a(v,u)\leq m$ for all $v$, with $m\in[0,\infty]$, then $W_n^a(v)\leq m^n$. If $m&lt;1$, then</p>
<div class="math-display">$$\sum_{n=0}^\infty W_n^a(v)\leq\frac1{1-m}&lt;\infty.$$</div>
<p>The same bounds apply to $a^\circ$ whenever its off-diagonal rows are bounded by $m$, with no restriction on the original diagonal entries of $a$.</p>
<p><em>Proof.</em> Split a sequence according to its first vertex $u$. Its weight is $a(v,u)$ times the weight of its remaining sequence rooted at $u$. Rearrangement and distributivity of nonnegative sums give the recurrence, with no symmetry or countability assumption. Inducting from $W_0^a(v)=1$ gives</p>
<div class="math-display">$$W_{n+1}^a(v)\leq\sum_u a(v,u)m^n=m^n\sum_u a(v,u)\leq m^{n+1}.$$</div>
<p>All operations take place in the extended nonnegative reals, so the estimate also covers $m=0$ and $m=\infty$, with $m^0=1$. For $m&lt;1$, sum over lengths and use the finite geometric series limit. Applying this result to $a^\circ$ proves the final assertion.</p>
<p>On a one-point space with kernel value $r$, there is exactly one sequence of each length and $W_n=r^n$, including $r=1$ and $r=\infty$. Thus the bound can be exact. If the original kernel is infinite on the diagonal and zero elsewhere, its diagonal-removed kernel is zero: its total walk weight is one, entirely from length zero. This illustrates why a hypothesis on the original diagonal would be inappropriate in the graph application.</p>

## From simple paths to sequence sums {#section-bonds}

<p>For a countable bond model with pair profile $q$, take $a(v,w)=q(\{v,w\})$ and remove its diagonal. A connection has a vertex-simple open path witness. Independence applies to that path because its edges are distinct, giving its open probability as the product of their probabilities. The countable union bound and the susceptibility identity yield</p>
<div class="math-display">$$\chi_q(v)\leq\sum_y\sum_{\gamma:v\to y\text{ simple}}\prod_{e\in\gamma}q(e)\leq\sum_{n=0}^\infty W_n^{a^\circ}(v).$$</div>
<p>For the second inequality, a simple path together with its endpoint is determined by the ordered list of vertices after $v$. Its edge product is precisely the weight of that sequence. Distinct paths therefore give distinct terms when the path sum is enlarged to all sequences. This is a comparison of deterministic nonnegative sums, with no independence assertion for repeated edges. The length-zero path supplies the root contribution one. The ordered edge-product identity and recovery of a path from its continuation list are deterministic facts and need no countability assumption.</p>
<p>The <a href="/tag/53Z9/">row-sum susceptibility theorem</a> follows whenever $\sum_{w\ne v}q(\{v,w\})\leq m&lt;1$ uniformly. Equivalently, apply that theorem after <a href="/tag/EYCQ/">removing the diagonal parameters</a>, which leaves graph observables unchanged. Finite expected cluster volume implies almost-sure finiteness at a fixed root, and countability gives one probability-one event on which all clusters are finite. If every off-diagonal probability is zero, the open graph is empty almost surely and $\chi_q(v)=1$, regardless of diagonal parameters.</p>

<p>For a finite host graph of maximum degree $\Delta$, probabilities at most $p$ on its edges and zero on other non-diagonal pairs give row sums at most $\Delta p$. Thus the same theorem gives $\chi_q(v)\leq(1-\Delta p)^{-1}$ when $\Delta p&lt;1$, with arbitrary diagonal probabilities. For the complete graph on $n\geq1$ vertices with constant off-diagonal probability $p$, the row is exactly $(n-1)p$. The bound holds at every root, and averaging it gives <a href="/tag/MIQ7/">the finite random graph estimate</a>. At $n=1$ the susceptibility is exactly one even if the loop coordinate is always open; at $n=0$ there is no root to evaluate. On three vertices at $p=1/4$, or on two vertices at $p=1/2$, the estimate is $\chi_q(v)\leq2$. Finite graphs have finite clusters at every parameter, so the row criterion is sufficient for this estimate and is not a criterion for finiteness of their clusters.</p>

## Finite intensities and possibly infinite thresholds {#section-intensity}

<a id="tag-BPR6" data-assertion="corollary" data-title="Off-diagonal intensity rows give susceptibility and threshold bounds"></a>
<p>Let $V$ be countable, let $J$ be a finite nonnegative symmetric pair intensity, and put $q_\beta(e)=1-e^{-\beta J(e)}$ for finite $\beta\geq0$. Suppose</p>
<div class="math-display">$$\sum_{w\ne v}J(\{v,w\})\leq M&lt;\infty\qquad\text{for every }v.$$</div>
<p>No restriction is imposed on diagonal intensities. If $\beta M&lt;1$, then</p>
<div class="math-display">$$1\leq\chi_\beta(v)\leq\frac1{1-\beta M}&lt;\infty,$$</div>
<p>and almost surely every cluster is finite. For $M&gt;0$, every rooted critical intensity and the global critical intensity are at least $M^{-1}$. If $M=0$, each susceptibility is one at every finite parameter and all these thresholds are infinite. Independently of a row bound, $\chi_0(v)=1$.</p>
<p>The thresholds here are the infima of finite parameters giving positive probability of an infinite cluster at the chosen root, or somewhere in the graph, respectively, with $\inf\varnothing=\infty$. They are not defined through divergence of susceptibility, and their definition supplies no percolation claim at the infimum.</p>
<p><em>Proof.</em> The profile starts at zero, increases with $\beta$, and satisfies $1-e^{-\beta J(e)}\leq\beta J(e)$. Therefore</p>
<div class="math-display">$$\sum_{w\ne v}q_\beta(\{v,w\})\leq\beta M.$$</div>
<p>Apply the preceding row bound and simultaneous finiteness argument. If $M&gt;0$, no finite parameter below $M^{-1}$ belongs to either percolating-parameter set; their infima are therefore at least $M^{-1}$, including when the sets are empty.</p>
<p>If $M=0$, nonnegativity forces every off-diagonal intensity to vanish. The same is true of the corresponding opening probabilities at every finite parameter. Countability makes all non-diagonal coordinates closed simultaneously almost surely, so every cluster is a singleton and both percolating-parameter sets are empty. Diagonal intensities may still be positive. At $\beta=0$, every coordinate probability is zero for any finite intensity profile, giving the last assertion without a row assumption.</p>
<p>On a finite vertex set every infinite-cluster threshold is infinite, even with nonzero intensities; on the empty vertex set the global percolation event is empty and there are no rooted thresholds to evaluate. The lower bound does not assert finiteness of a threshold or decide percolation at $\beta M=1$.</p>

---
{
  "id": "subcritical-bound",
  "title": "A small-parameter susceptibility bound",
  "subtitle": "A complete argument from paths to finite clusters",
  "kind": "theorem",
  "category": "General theory",
  "summary": "A uniform row-sum bound below one controls susceptibility without transitivity or local finiteness of the host.",
  "context": [
    "$V$ is countable and $G$ is an undirected simple graph.",
    "Edges are independent, with $q(e)\\in[0,1]$.",
    "Extend $q(v,w)$ by zero on nonedges and on the diagonal.",
    "$\\chi_q(v)=\\mathbb E_q|K_v|$ denotes the susceptibility at $v$."
  ],
  "related": [
    "criticality",
    "sharpness",
    "finite-random-graphs"
  ],
  "sourceIds": [
    "notes",
    "hutchcroft-powerlaw-2021"
  ],
  "aliases": [
    "path counting",
    "row sum",
    "geometric series",
    "subcritical",
    "beta c lower bound"
  ],
  "prototypeUses": [
    "product-model",
    "connectivity",
    "susceptibility"
  ]
}
---

## The theorem {#section-statement}

<a id="tag-53Z9" data-assertion="theorem" data-title="Uniform row-sum susceptibility bound and cluster finiteness"></a><div class="theorem-statement"><p>Let $0\le m&lt;1$, and suppose that</p><div class="math-display">$$\sum_{w\in V}q(v,w)\le m\qquad\text{for every }v\in V.$$</div><p>Then, for every vertex $v$,</p><div class="math-display">$$\chi_q(v)\le \frac1{1-m}.$$</div><p>Moreover, with probability one, every open cluster is finite.</p></div><p>No connectedness, transitivity, or local finiteness of the host is needed. The bound includes the length-zero connection: even with no open edges, $\chi_q(v)=1$.</p>

## 1. Use simple path witnesses {#section-proof-paths}

<a id="tag-YFF7" data-assertion="proposition" data-title="Probability of a simple open path"></a><p>If $v\leftrightarrow w$, there is a <a href="#/connectivity">finite vertex-simple open path</a> $\gamma$ from $v$ to $w$. Its edges are distinct, so <a href="#/product-model">independence under the product law</a> gives</p><div class="math-display">$$\mathbb P_q(\gamma\text{ is open})=\prod_{e\in\gamma}q(e).$$</div><a id="tag-5C44" data-assertion="proposition" data-title="Simple-path union bound"></a><p>Taking a union bound over these path witnesses bounds each connection probability. Countability makes this a countable union. Repeated traversals of an edge are not independent trials; this is why the witnesses are simple paths.</p>

## 2. Enlarge the deterministic sum {#section-proof-walks}

<p>After summing over the endpoint, enlarge the sum of simple-path weights to the sum of all walk weights. This is a deterministic inequality between nonnegative sums, not a probability formula for open walks.</p><a id="tag-I9QY" data-assertion="definition" data-title="Total weight of walks of fixed length"></a><p>For $n\ge0$, put</p><div class="math-display">$$W_n(v)=\sum_{v_1,\ldots,v_n\in V}\prod_{i=1}^n q(v_{i-1},v_i),\qquad v_0=v.$$</div><p>The empty product gives $W_0(v)=1$. Every simple path counted above is among these vertex sequences.</p>

## 3. Bound every walk length {#section-proof-recurrence}

<a id="tag-UMQY" data-assertion="proposition" data-title="Walk-weight recurrence and geometric bound"></a><p>Rearranging nonnegative sums yields</p><div class="math-display">$$W_{n+1}(v)=\sum_u q(v,u)W_n(u).$$</div><p>Inductively, if $W_n(u)\le m^n$ for every $u$, then $W_{n+1}(v)\le m^n\sum_uq(v,u)\le m^{n+1}$. Hence $W_n(v)\le m^n$ at every vertex and every length.</p>

## 4. Sum the geometric series {#section-proof-sum}

<a id="tag-F12C" data-assertion="proposition" data-title="Susceptibility bounded by the walk-weight sum"></a><p>The preceding bounds give</p><div class="math-display">$$\chi_q(v)=\sum_w\mathbb P_q(v\leftrightarrow w)\le\sum_{n\ge0}W_n(v)\le\sum_{n\ge0}m^n=\frac1{1-m}.$$</div><p>All changes of summation order are justified by nonnegativity. No finiteness of susceptibility was assumed during the argument.</p>

## 5. Pass from expectation to almost-sure finiteness {#section-proof-finiteness}

<a id="tag-012G" data-assertion="proposition" data-title="Simultaneous cluster finiteness on a countable host"></a><p>The <a href="#/susceptibility">susceptibility identity</a> now gives a finite expected extended cluster volume. Consequently $\mathbb P_q(|K_v|=\infty)=0$ for each $v$. Taking a countable union over $V$ proves that there are almost surely no infinite clusters anywhere.</p><p>This last step uses countability. It asserts simultaneous finiteness at all vertices under this fixed law, not a common null set for an uncountable family of parameters.</p>

## Consequence for an intensity family {#section-intensity}

<a id="tag-E771" data-assertion="corollary" data-title="Susceptibility bound for the intensity family"></a><p>If $\sum_wJ(v,w)\le M&lt;\infty$ uniformly, then $1-e^{-t}\le t$ gives $\sum_wq_\beta(v,w)\le\beta M$. Therefore</p><div class="math-display">$$\beta M&lt;1\quad\Longrightarrow\quad\chi_\beta(v)\le\frac1{1-\beta M}.$$</div><a id="tag-JZ47" data-assertion="corollary" data-title="Lower bound on critical intensities including zero kernel"></a><p>For $M&gt;0$, every root threshold and the global <a href="#/criticality">critical intensity</a> are at least $M^{-1}$. When $M=0$, all intensities vanish and these thresholds are infinite. This argument gives no conclusion about percolation at $\beta=M^{-1}$ or at the actual critical point.</p>

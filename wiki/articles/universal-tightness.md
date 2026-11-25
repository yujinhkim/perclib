---
{
  "id": "universal-tightness",
  "title": "Universal tightness of maximum clusters",
  "subtitle": "A quantile sets the scale without a geometry.",
  "kind": "theorem",
  "category": "Cluster geometry",
  "summary": "The largest cluster intersection with a finite region has exponentially small upper tails and a controlled lower tail, relative to a canonical quantile. No transitivity or critical tuning is needed.",
  "context": [
    "A countable weighted graph carries independent bond percolation with edge probabilities 1 − exp(−βJ_e).",
    "The observation set Λ is finite and nonempty.",
    "Clusters are formed in the whole graph; paths may leave Λ and return."
  ],
  "related": [
    "susceptibility",
    "cutoff-families",
    "hierarchical-two-point",
    "finite-random-graphs"
  ],
  "sourceIds": [
    "hutchcroft-powerlaw-2021",
    "notes"
  ],
  "aliases": [
    "maximum cluster",
    "largest cluster",
    "quantile",
    "maximum cluster tightness",
    "BK splitting"
  ],
  "prototypeUses": [
    "product-model",
    "connectivity"
  ]
}
---

## Choose the observable before the scale {#section-scale}

<a id="tag-GJIW" data-assertion="definition" data-title="Maximum cluster intersection and its quantile scale"></a><p>For a nonempty finite observation set $\Lambda$, let</p>
      $$Z_\Lambda=\max_{x\in\Lambda}|K_x\cap\Lambda|,\qquad
      M=\min\{n\ge1:\mathbb P_\beta(Z_\Lambda\ge n)\le e^{-1}\}.$$
      <a id="tag-AU8B" data-assertion="proposition" data-title="Deterministic bounds on the maximum and quantile"></a><p>Thus $1\le Z_\Lambda\le|\Lambda|$ and $2\le M\le|\Lambda|+1$. Ties do not require a choice of a “largest cluster”: only its intersection size is used. The observable uses <a href="#/connectivity">full-cluster intersections</a> with the set $\Lambda$: paths may leave it before returning.</p><p>When the whole host is finite and the observation set contains every vertex, this is the largest component of a <a href="#/finite-random-graphs">finite random graph</a>.</p>

## Two-sided control at the quantile scale {#section-statement}

<a id="tag-4724" data-assertion="theorem" data-title="Universal upper and lower tails at the quantile scale"></a><p>For the <a href="#/product-model">independent weighted model</a>, the universal tightness theorem gives</p>
      $$\mathbb P_\beta(Z_\Lambda\ge\lambda M)\le e^{-\lambda/9}\qquad(\lambda\ge1),$$
      $$\mathbb P_\beta(Z_\Lambda&lt;\varepsilon M)\le27\varepsilon\qquad(0&lt;\varepsilon\le1).$$
      <a id="tag-21D4" data-assertion="theorem" data-title="Rooted upper-tail refinement"></a><p>The same constants apply to every graph, every finite nonempty observation set, and every parameter. A rooted refinement is</p>
      $$\mathbb P_\beta(|K_u\cap\Lambda|\ge\lambda M)
      \le e^{1-\lambda/9}\mathbb P_\beta(|K_u\cap\Lambda|\ge M)
      \qquad(\lambda\ge1).$$
      <p>The theorem controls fluctuations around $M$. Determining how $M$ depends on the size of a Euclidean or hierarchical ball remains a separate problem.</p>

## The combinatorial mechanism {#section-mechanism}

<p>A large connected witness can be split into many connected witnesses whose edge sets are disjoint. The BK inequality then bounds their disjoint occurrence by a product of probabilities. The witnesses may share vertices; the required disjointness concerns edges.</p>
      <p>Iterating this splitting gives an amplification inequality for the upper tail. Applying the same inequality between a small scale and the defining quantile controls the lower tail. Infinite hosts are handled by finite subgraphs and monotone limits. This is a proof outline; the splitting lemma is a substantial separate dependency.</p>

## From tails to moments {#section-moments}

<a id="tag-2FN1" data-assertion="corollary" data-title="Uniform moment bound at the quantile scale"></a><p>A useful consequence follows by tail integration, the same principle behind the <a href="#/susceptibility">susceptibility tail-sum identity</a>. For every fixed integer $k\ge1$, there is a constant $C_k$ independent of the graph such that</p>
      $$\mathbb E_\beta[Z_\Lambda^k]\le C_k M^k.$$
      <a id="tag-AWWZ" data-assertion="corollary" data-title="Expected maximum comparable to the quantile scale"></a><p>Indeed, split $k\int_0^\infty t^{k-1}\mathbb P(Z_\Lambda&gt;t)\,dt$ at $M$, and use the exponential estimate above $M$. Conversely, the definition of $M$ gives $\mathbb P(Z_\Lambda\ge M-1)&gt;e^{-1}$, so $\mathbb E Z_\Lambda\ge(M-1)e^{-1}\ge M/(2e)$.</p>
      <p>This converts a quantile estimate into moment control, a useful interface for <a href="#/cutoff-families">cutoff arguments</a> and <a href="#/hierarchical-two-point">hierarchical renormalisation</a>.</p>

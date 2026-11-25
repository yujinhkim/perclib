---
{
  "id": "product-model",
  "title": "Product percolation",
  "subtitle": "One probability space, many geometries",
  "kind": "model",
  "category": "Foundations",
  "summary": "Independent coordinates provide a common language for finite random graphs, lattice percolation, and summable long-range models.",
  "context": [
    "A finite or countable vertex set $V$.",
    "An undirected simple host graph $G=(V,E)$.",
    "An edge profile $q:E\\to[0,1]$."
  ],
  "related": [
    "connectivity",
    "finite-random-graphs",
    "cutoff-families"
  ],
  "sourceIds": [
    "grimmett",
    "heydenreich-hofstad",
    "mathlib",
    "notes"
  ],
  "aliases": [
    "Bernoulli",
    "independent edges",
    "configuration space",
    "q beta J",
    "bond percolation",
    "site percolation"
  ],
  "prototypeUses": []
}
---

## The configuration law {#section-law}

<a id="tag-8NWX" data-assertion="definition" data-title="Configuration and product Bernoulli law"></a><p>A configuration is a function $\omega:E\to\{0,1\}$. The edge $e$ is open when $\omega(e)=1$. Equip $\Omega=\{0,1\}^E$ with the product sigma-algebra and the probability law</p><div class="math-display">$$\mathbb P_q=\bigotimes_{e\in E}\operatorname{Bernoulli}(q(e)).$$</div><a id="tag-5PAT" data-assertion="proposition" data-title="Finite cylinder probabilities"></a><p>For finite disjoint edge sets $F,H$, the cylinder formula is</p><div class="math-display">$$\mathbb P_q\bigl(\omega|_F=1,\ \omega|_H=0\bigr)=\prod_{e\in F}q(e)\prod_{e\in H}(1-q(e)).$$</div><p>This formula determines the measure. Independence is a property of this law, rather than a property of a configuration or a graph.</p>

## Parameterised families {#section-families}

<a id="tag-A65C" data-assertion="definition" data-title="Homogeneous and exponential intensity families"></a><p>Homogeneous bond percolation takes $q(e)=p$. On a complete finite host this gives the <a href="#/finite-random-graphs">Erdős–Rényi random graph</a>. For a finite nonnegative intensity $J(e)$, the exponential family is</p><div class="math-display">$$q_\beta(e)=1-\exp(-\beta J(e)),\qquad \beta\ge0.$$</div><p>The same product construction supports both families. Their parameter derivatives differ, so a change from $p$ to $\beta$ must be recorded. A family $pD(e)$ is not generally a fixed-$J$ exponential family with a renamed parameter.</p><a id="tag-2ML7" data-assertion="proposition" data-title="Monotone product coupling"></a><p>Independent uniform variables give a monotone coupling: $\omega_q(e)=\mathbf1_{\{U_e\le q(e)\}}$. Thus $q\le q'$ yields $\omega_q\le\omega_{q'}$ edgewise, simultaneously.</p><p><a href="#/cutoff-families">Cutoff families</a> vary the kernel through a spatial scale. The same monotone coupling then compares different cutoff scales, as well as different intensities.</p>

## What the model does—and does not—assume {#section-scope}

<a id="tag-I24D" data-assertion="proposition" data-title="Summable incident probabilities imply finite open degrees"></a><p>The host need not be locally finite. A long-range model can have infinitely many possible edges at each vertex. If $\sum_{e\ni v}q(e)&lt;\infty$, the expected open degree at $v$ is finite, so its open degree is finite almost surely. Countability then gives one probability-one event on which every open degree is finite.</p><p>Site percolation uses independent vertex coordinates instead. Dependent models can share the configuration and event vocabulary but require their own laws; product-measure arguments do not transfer automatically.</p><p><a href="#/connectivity">Connectivity through finite open paths</a> defines the open clusters. Their expected volumes are measured by <a href="#/susceptibility">susceptibility</a>.</p>

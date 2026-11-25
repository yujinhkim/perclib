---
{
  "id": "triangle-condition",
  "title": "The triangle condition",
  "subtitle": "A diagrammatic criterion for mean-field volume behaviour.",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "A summability condition on three two-point functions controls several critical exponents. The criterion and the model-dependent proof of the criterion are separate mathematical results.",
  "context": [
    "Independent nearest-neighbour bond percolation on $\\mathbb Z^d$, with $d\\ge2$.",
    "The triangle diagram is evaluated at the infinite-volume critical parameter p_c.",
    "The notation f ≍ g means upper and lower bounds by positive constants in the stated regime."
  ],
  "related": [
    "sharpness",
    "exploration",
    "hierarchical-two-point",
    "cutoff-families"
  ],
  "sourceIds": [
    "hutchcroft-triangle-2021",
    "heydenreich-hofstad",
    "notes"
  ],
  "aliases": [
    "triangle diagram",
    "mean-field exponents",
    "mean field",
    "critical cluster-volume exponent",
    "Aizenman–Newman"
  ],
  "prototypeUses": [
    "product-model",
    "connectivity",
    "susceptibility",
    "criticality"
  ]
}
---

## The diagram {#section-diagram}

<a id="tag-67VP" data-assertion="definition" data-title="Triangle diagram"></a><p>For the <a href="#/product-model">independent lattice model</a>, write $\tau_p(x,y)=\mathbb P_p(x\leftrightarrow y)$ for the <a href="#/connectivity">two-point function</a>. The rooted triangle diagram is the nonnegative, possibly infinite sum</p>
      $$\nabla_p=\sum_{x,y\in\mathbb Z^d}\tau_p(0,x)\,\tau_p(x,y)\,\tau_p(y,0).$$
      <a id="tag-7UDJ" data-assertion="definition" data-title="Critical triangle condition"></a><p>The <strong>triangle condition</strong> is $\nabla_{p_c}&lt;\infty$, evaluated at the <a href="#/criticality">critical parameter</a>. Each factor records a connection along one side of a triangle. Summing over its two free vertices measures how strongly three connections can interact across all scales.</p>
      <p>The formula is a definition on more general countable graphs too. A theorem using it must still state the symmetry and model assumptions under which the conclusion has been proved.</p>

## A conditional mean-field theorem {#section-consequences}

<a id="tag-2ZI0" data-assertion="theorem" data-title="Mean-field estimates under the triangle condition"></a><div class="theorem-statement"><p>Assume that the critical triangle diagram is finite: $\nabla_{p_c}&lt;\infty$. Then</p>
      $$\chi(p)\asymp(p_c-p)^{-1}\quad\text{as }p\uparrow p_c,$$
      $$\mathbb P_{p_c}(|K_0|\ge n)\asymp n^{-1/2}\quad(n\ge1),$$
      $$\theta(p)\asymp p-p_c\quad\text{as }p\downarrow p_c.$$</div>
      <a id="tag-P9JD" data-assertion="corollary" data-title="Critical nonpercolation and infinite susceptibility"></a><p>These are the mean-field <a href="#/susceptibility">susceptibility</a>, critical cluster-volume, and order-parameter behaviours. The middle estimate also implies $\theta(p_c)=0$ and, by the tail-sum formula, $\chi(p_c)=\infty$.</p>
      <p>The susceptibility estimate strengthens the subcritical finiteness supplied by <a href="#/sharpness">sharpness</a>. Applying the theorem to a particular dimension or kernel requires a separate proof that its critical triangle diagram is finite.</p>

## Why the diagram enters {#section-proof-architecture}

<p>Differentiating a connection probability exposes pivotal edges. Comparing configurations with and without such an edge creates products of connection probabilities; controlling overlaps produces diagrammatic sums. Triangle finiteness bounds the cumulative correction and permits integration of differential inequalities.</p>
      <p>The <a href="#/exploration">exploration</a> viewpoint explains which edges have been revealed. Disjoint occurrence estimates control simultaneous connection witnesses. These are different ingredients, and neither should be replaced by an unjustified assertion that the whole connection events are independent.</p>

## Spatial estimates and quantitative variants {#section-scope}

<p>Cluster volume and Euclidean radius are different observables. A pointwise estimate for $\tau_{p_c}(0,x)$, an extrinsic one-arm exponent, or the spatial motion of a backbone needs further geometric information. A <a href="#/hierarchical-two-point">hierarchical two-point theorem</a> is one such model-specific input.</p>
      <p>Quantitative versions track the size of the diagram. Versions allowing a controlled logarithmic divergence lead to different conclusions with logarithmic losses; they are separate statements rather than instances of the finite-triangle hypothesis.</p>

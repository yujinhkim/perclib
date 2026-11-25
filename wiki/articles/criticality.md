---
{
  "id": "criticality",
  "title": "Criticality and critical windows",
  "subtitle": "Thresholds on infinite graphs, scales on finite ones",
  "kind": "concept",
  "category": "Observables",
  "summary": "An infinite-cluster threshold and a finite-size critical window answer different questions.",
  "context": [
    "For the intensity model, $\\beta\\in[0,\\infty)$ and the law is monotone in $\\beta$.",
    "Thresholds take values in $[0,\\infty]$; the infimum of the empty set is infinity."
  ],
  "related": [
    "subcritical-bound",
    "sharpness",
    "finite-random-graphs",
    "hierarchical-two-point"
  ],
  "sourceIds": [
    "grimmett",
    "heydenreich-hofstad",
    "notes"
  ],
  "aliases": [
    "pc",
    "βc",
    "critical threshold",
    "phase transition",
    "critical window",
    "finite size"
  ],
  "prototypeUses": [
    "product-model",
    "connectivity"
  ]
}
---

## Infinite-volume thresholds {#section-infinite}

<a id="tag-8DAH" data-assertion="definition" data-title="Root percolation probability and critical intensity"></a><p>For an <a href="#/product-model">intensity family</a> and the <a href="#/connectivity">open cluster</a> at a root $v$, define</p><div class="math-display">$$\theta_v(\beta)=\mathbb P_\beta(|K_v|=\infty),\qquad\beta_c(v)=\inf\{\beta\ge0:\theta_v(\beta)&gt;0\}.$$</div><a id="tag-JZN0" data-assertion="proposition" data-title="Global threshold is the infimum of rooted thresholds"></a><p>The global threshold uses the event that some infinite cluster exists. On a countable vertex set this event is the union of the rooted events, so</p><div class="math-display">$$\beta_c^{\mathrm{global}}=\inf_{v\in V}\beta_c(v).$$</div><a id="tag-XONW" data-assertion="proposition" data-title="Root thresholds agree under transitivity"></a><p>Under a transitive law the rooted probabilities, and hence their thresholds, agree. On disconnected or inhomogeneous models this equality between different roots must not be presumed.</p>

## What a threshold does not decide {#section-endpoints}

<p>Monotonicity separates the regimes below and above the threshold, but does not itself determine what happens at the threshold. Continuity of the phase transition is an additional theorem, with model-dependent hypotheses.</p><p>The <a href="#/subcritical-bound">row-sum bound</a> supplies a positive lower bound on a critical intensity when the incident intensity is uniformly bounded. It does not prove that the threshold is finite.</p><p>Expressions such as $\mathbb P_{\beta_c}$ require a defined critical-parameter law. In an intensity model, one convenient approach is to prove $\beta_c&lt;\infty$ before using it as an ordinary real parameter.</p><p><a href="#/sharpness">Sharpness</a> concerns finiteness of <a href="#/susceptibility">susceptibility</a> below the threshold and quantitative growth of the infinite-cluster probability above it.</p>

## Finite graphs need another notion {#section-finite}

<a id="tag-KB1L" data-assertion="proposition" data-title="Infinite-cluster threshold on finite hosts"></a><p>On a finite graph every cluster is finite, at every finite intensity. The infinite-cluster definition therefore gives $\beta_c=\infty$ and says nothing about the abrupt emergence of large components.</p><a id="tag-X9N1" data-assertion="definition" data-title="Erdős–Rényi critical-window scale"></a><p>For a sequence of finite graphs, a critical window describes parameter scales on which component geometry changes. In the Erdős–Rényi example, one studies</p><div class="math-display">$$p=\frac1n+\lambda n^{-4/3},\qquad \lambda\in\mathbb R,$$</div><p>with fixed $\lambda$ as $n\to\infty$. Component sizes are studied on the $n^{2/3}$ scale. For <a href="#/finite-random-graphs">finite random graphs</a>, the window is characterised by component statistics; its normalisation and hypotheses depend on the graph family.</p>

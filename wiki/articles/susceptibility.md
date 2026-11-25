---
{
  "id": "susceptibility",
  "title": "Susceptibility",
  "subtitle": "The expected volume seen from a root",
  "kind": "concept",
  "category": "Observables",
  "summary": "Susceptibility connects an expected cluster volume to a spatial sum of connection probabilities.",
  "context": [
    "A countable vertex set and a specified percolation law.",
    "Cluster volume and expectation are allowed to be infinite."
  ],
  "related": [
    "subcritical-bound",
    "sharpness",
    "triangle-condition",
    "finite-random-graphs"
  ],
  "sourceIds": [
    "grimmett",
    "heydenreich-hofstad",
    "notes"
  ],
  "aliases": [
    "chi",
    "χ",
    "expected cluster size",
    "susceptibility identity",
    "tail sum",
    "truncated susceptibility"
  ],
  "prototypeUses": [
    "product-model",
    "connectivity"
  ]
}
---

## Definition and the sum identity {#section-definition}

<a id="tag-8DSI" data-assertion="definition" data-title="Susceptibility and the two-point sum identity"></a><p>The susceptibility at $v$ is the expected volume of its <a href="#/connectivity">open cluster</a>:</p><div class="math-display">$$\chi_q(v)=\mathbb E_q|K_v|=\sum_{w\in V}\tau_q(v,w)\in[1,\infty].$$</div><p>The equality is an application of nonnegative integration. Pointwise, the cluster volume is $\sum_w\mathbf1_{\{v\leftrightarrow w\}}$. Tonelli's theorem permits exchanging this nonnegative sum and expectation, including when the answer is infinite.</p><a id="tag-QXWF" data-assertion="proposition" data-title="Root independence under transitivity"></a><p>Under a transitive law the value is independent of the root. Without that assumption, retaining $v$ in the notation matters.</p>

## The same quantity through tails {#section-tails}

<a id="tag-CSY8" data-assertion="proposition" data-title="Tail-sum identity"></a><p>For a nonnegative integer-valued variable, including extended values,</p><div class="math-display">$$\mathbb E X=\sum_{n\ge1}\mathbb P(X\ge n).$$</div><p>Apply this to $|K_v|$. The index begins at one: a singleton cluster has susceptibility one. This is an exact identity; later estimates of the sum may be asymptotic.</p><a id="tag-INZI" data-assertion="proposition" data-title="Finite expectation implies almost-sure finiteness"></a><p>Finite susceptibility implies $|K_v|&lt;\infty$ almost surely. The converse is false for general random variables: an almost surely finite variable can have infinite mean. Percolation theorems connecting these two notions therefore contain real mathematical content.</p>

## Related quantities with different meanings {#section-variants}

<a id="tag-MTJT" data-assertion="definition" data-title="Truncated susceptibility"></a><p>The truncated susceptibility is $\mathbb E_q[|K_v|;|K_v|&lt;\infty]$, where the variable is defined to be zero on infinite clusters. It differs from ordinary susceptibility in the <a href="#/criticality">supercritical phase</a>.</p><a id="tag-BX1L" data-assertion="definition" data-title="Restricted and intersection susceptibilities"></a><p>For a region $\Lambda$ containing $v$, there are two natural finite-region quantities:</p><div class="math-display">$$\chi_q^\Lambda(v)=\mathbb E_q|K_v^\Lambda|,\qquad \widetilde\chi_q^\Lambda(v)=\mathbb E_q|K_v\cap\Lambda|.$$</div><p>They agree only when the relevant outside connections cannot matter. A three-vertex path whose middle vertex is outside the region already gives a counterexample.</p>

## Why susceptibility is a central interface {#section-uses}

<a id="tag-EDWA" data-assertion="proposition" data-title="Monotonicity of susceptibility"></a><p>The <a href="#/product-model">monotone product coupling</a> makes susceptibility nondecreasing with the edge profile. The <a href="#/subcritical-bound">row-sum theorem</a> provides a quantitative finite upper bound in a simple regime. <a href="#/sharpness">Sharpness</a> extends finiteness throughout the subcritical phase under the relevant homogeneity assumptions. The <a href="#/triangle-condition">triangle condition</a> controls its rate of divergence near criticality.</p><p>For <a href="#/finite-random-graphs">finite random graphs</a>, susceptibility is also a normalized sum of squared component sizes. This identity links the rooted viewpoint to the collection of all components.</p>

---
{
  "id": "cutoff-families",
  "title": "Cutoff families for long-range kernels",
  "subtitle": "Grow the interaction through a continuous spatial scale.",
  "kind": "method",
  "category": "Long-range methods",
  "summary": "A cutoff is a family of models, not just a finite box. Its exact definition determines which edges change as the scale varies, and therefore which differential identities are available.",
  "context": [
    "The vertex set is the integer lattice in dimension d ≥ 1, with a fixed norm and distinct vertices x, y.",
    "The decay parameter satisfies α > 0; the cutoff scale r is positive.",
    "The displayed family has full kernel J(x,y) = ‖x−y‖^(−d−α)/(d+α) and intensity parameter β ≥ 0."
  ],
  "related": [
    "universal-tightness",
    "triangle-condition",
    "criticality",
    "exploration"
  ],
  "sourceIds": [
    "notes",
    "hutchcroft-lrp-1",
    "hutchcroft-lrp-2"
  ],
  "aliases": [
    "integrated cutoff",
    "hard cutoff",
    "truncated kernel",
    "cutoff renormalisation",
    "cutoff renormalization",
    "Russo formula"
  ],
  "prototypeUses": [
    "product-model",
    "connectivity",
    "susceptibility"
  ]
}
---

## An integrated cutoff {#section-definition}

<a id="tag-PVA8" data-assertion="definition" data-title="Integrated cutoff kernel"></a><p>Put $a=d+\alpha$ and $s=\|x-y\|&gt;0$. Define</p>
      $$J_r(x,y)=\mathbf1_{\{s\le r\}}\int_s^r t^{-a-1}\,dt
      =\frac{(s^{-a}-r^{-a})_+}{a},\qquad J_r(x,x)=0.$$
      <a id="tag-MQNP" data-assertion="proposition" data-title="Monotonicity and limit of the cutoff family"></a><p>The edge-opening probabilities are $q_{\beta,r}(x,y)=1-e^{-\beta J_r(x,y)}$. As $r$ increases, every $J_r(x,y)$ increases to the full kernel $J(x,y)=s^{-a}/a$. The <a href="#/product-model">monotone product coupling</a> therefore couples all scales in an increasing way.</p>

## Compare with hard truncation {#section-comparison}

<a id="tag-LF50" data-assertion="proposition" data-title="Difference between integrated and hard cutoff kernels"></a><p>The hard truncation would use $J(x,y)\mathbf1_{\{s\le r\}}$. For an edge already inside the cutoff, the integrated family instead has</p>
      $$J(x,y)-J_r(x,y)=\frac{r^{-a}}a\qquad(0&lt;s\le r).$$
      <p>Even short edges are weakened. Increasing $r$ strengthens all currently eligible edges as well as admitting new lengths. Replacing this family by hard truncation would change the derivative and the proof.</p>
      <p><a href="#/connectivity">Restricting connectivity to an observation box</a> is a third construction: it changes which vertices or paths are observed. A cutoff model on the full lattice still has infinitely many vertices.</p>

## Differentiate the family actually defined {#section-derivative}

<a id="tag-6YYS" data-assertion="proposition" data-title="Derivatives of the cutoff kernel and edge probability"></a><p>For fixed $x\ne y$, away from the corner $r=s$ one has</p>
      $$\frac{d}{dr}J_r(x,y)=\mathbf1_{\{s&lt;r\}}r^{-d-\alpha-1},$$
      $$\frac{d}{dr}q_{\beta,r}(x,y)
      =\beta e^{-\beta J_r(x,y)}
        \mathbf1_{\{s&lt;r\}}r^{-d-\alpha-1}.$$
      <a id="tag-4OFD" data-assertion="proposition" data-title="Finite-edge Russo derivative along the cutoff family"></a><p>These identities hold almost everywhere in $r$; one-sided derivatives can be specified at the corner. On a finite set of independent edges, the chain rule and Russo's formula give, for an increasing event $A$,</p>
      $$\frac{d}{dr}\mathbb P_{\beta,r}(A)
        =\sum_e\frac{d q_{\beta,r}(e)}{dr}\,
          \mathbb P_{\beta,r}(e\text{ is pivotal for }A).$$
      <p>Passing this identity to infinitely many edges requires its own convergence argument. Monotonicity alone does not justify interchanging an infinite sum with differentiation.</p>

## What a cutoff argument tracks {#section-observables}

<p>Typical observables include the <a href="#/susceptibility">susceptibility</a> $\chi_r=\mathbb E_{\beta,r}|K_0|$, higher cluster-size moments, and spatially weighted two-point sums. A pivotal edge can merge two components, so differentiation naturally introduces products of cluster masses and connection diagrams.</p>
      <p><a href="#/universal-tightness">Universal tightness</a> can control exceptionally large clusters. <a href="#/triangle-condition">Diagram estimates</a> control interactions between branches. Neither supplies the spatial scale for free: volume estimates and geometric moment estimates must be recorded separately.</p>
      <p>Consequently, a differential estimate depends on the chosen cutoff family and observable as well as the percolation law. A change of cutoff can change the derivative even when the full limiting kernel is unchanged.</p>

---
{
  "id": "finite-random-graphs",
  "title": "Finite random graphs and critical windows",
  "subtitle": "Use component statistics when infinite clusters are impossible.",
  "kind": "model",
  "category": "Finite-size percolation",
  "summary": "On a finite graph every cluster is finite. Component moments, largest-component scales, and critical windows replace the infinite-cluster event.",
  "context": [
    "The host graph has n ≥ 1 vertices and independent edge states.",
    "The root U is chosen uniformly from the vertices, independently of the percolation configuration.",
    "The Erdős–Rényi specialization is independent bond percolation on the complete graph K_n."
  ],
  "related": [
    "criticality",
    "exploration",
    "universal-tightness"
  ],
  "sourceIds": [
    "heydenreich-hofstad",
    "notes"
  ],
  "aliases": [
    "Erdős–Rényi",
    "Erdos Renyi",
    "G(n,p)",
    "finite-size scaling",
    "critical window",
    "largest component",
    "component partition"
  ],
  "prototypeUses": [
    "product-model",
    "connectivity",
    "susceptibility",
    "subcritical-bound"
  ]
}
---

## Susceptibility from the component partition {#section-identity}

<a id="tag-CY0D" data-assertion="proposition" data-title="Conditional cluster volume from the component partition"></a><p>For a realised configuration, write its <a href="#/connectivity">connected components</a> as $C_1,\ldots,C_m$. Conditional on that configuration, a uniform root falls in $C_i$ with probability $|C_i|/n$. Therefore</p>
      $$\mathbb E\bigl[|K_U|\mid\omega\bigr]
        =\frac1n\sum_{i=1}^m|C_i|^2.$$
      <a id="tag-XCGS" data-assertion="proposition" data-title="Average susceptibility as the second component moment"></a><p>Averaging over configurations gives the finite-graph <a href="#/susceptibility">susceptibility</a>:</p>
      $$\overline\chi=\frac1n\sum_v\mathbb E|K_v|
        =\frac1n\mathbb E\sum_i|C_i|^2.$$
      <p>This identity is exact for every finite host. A fixed root has the same susceptibility as the average only when a symmetry or another argument establishes it.</p>

## A concrete subcritical calculation {#section-erdos-renyi}

<a id="tag-MIQ7" data-assertion="corollary" data-title="Subcritical Erdős–Rényi susceptibility bound"></a><p>In $G(n,p)$, the <a href="#/product-model">product law</a> opens each edge independently with probability $p$. Each vertex has $n-1$ potential neighbours, so the row sum is $(n-1)p$. The <a href="#/subcritical-bound">path-counting theorem</a> gives</p>
      $$(n-1)p&lt;1\quad\Longrightarrow\quad
      \overline\chi\le\frac1{1-(n-1)p}.$$
      <a id="tag-PXP9" data-assertion="corollary" data-title="Subcritical largest-component tail bound"></a><p>Under the same subcritical hypothesis $(n-1)p&lt;1$, let $L_1=\max_i|C_i|$. Since $L_1^2\le\sum_i|C_i|^2$, Markov's inequality then gives, for every $r&gt;0$,</p>
      $$\mathbb P(L_1\ge r)\le
      \frac{n}{r^2[1-(n-1)p]}.$$
      <p>The estimate is useful when its right-hand side is small. It is an elementary bound, not a sharp description of the critical window.</p>

## The critical-window viewpoint {#section-window}

<a id="tag-F9EV" data-assertion="proposition" data-title="Erdős–Rényi critical-window component scale"></a><p>For Erdős–Rényi graphs, the classical <a href="#/criticality">critical window</a> is parametrised by</p>
      $$p=\frac1n+\lambda n^{-4/3},\qquad \lambda\in\mathbb R\text{ fixed},$$
      <p>with largest components on the $n^{2/3}$ scale as $n\to\infty$. This is a statement about a sequence of finite models and their component distributions. It cannot be expressed as the appearance of an actually infinite cluster in one finite graph.</p>
      <p>A precise scaling-limit theorem must specify its mode of convergence, ordering of components, and state space. The component scale alone does not determine the joint limiting law.</p>

## Exploration and other finite hosts {#section-connections}

<p><a href="#/exploration">Component exploration</a> turns a random graph into a queue process: discovering a vertex adds its previously unseen neighbours. The process suggests branching approximations in sparse regimes and a different scaling analysis near the critical window.</p>
      <p>Finite tori and hypercubes also have critical-window questions, but their geometry and dependence between explored connections require their own estimates. The component-moment identity and <a href="#/universal-tightness">universal maximum-cluster bounds</a> still apply to these finite hosts. Their critical parameters and window widths remain model-specific.</p>

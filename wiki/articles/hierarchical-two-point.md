---
{
  "id": "hierarchical-two-point",
  "title": "Critical two-point function on the hierarchical lattice",
  "subtitle": "A model-specific power law with a reusable dependency chain.",
  "kind": "theorem",
  "category": "Hierarchical percolation",
  "summary": "For a radial hierarchical kernel comparable to a power law, critical connection probabilities have a matching power-law upper and lower bound throughout the regime 0 < α < d.",
  "context": [
    "Integers $d\\ge1$ and $L\\ge2$ define the hierarchical lattice.",
    "The intensity kernel $J$ is nonnegative and radial: it depends only on the hierarchical distance.",
    "Edges are independent, with probabilities $1-\\exp(-\\beta J(x-y))$ at intensity $\\beta\\ge0$."
  ],
  "related": [
    "sharpness",
    "universal-tightness",
    "triangle-condition",
    "cutoff-families"
  ],
  "sourceIds": [
    "hutchcroft-hierarchical-2021",
    "notes"
  ],
  "aliases": [
    "hierarchical lattice",
    "hierarchical two-point function",
    "ultrametric",
    "hierarchical long-range percolation",
    "critical two point"
  ],
  "prototypeUses": [
    "product-model",
    "connectivity",
    "criticality",
    "susceptibility"
  ]
}
---

## The hierarchical geometry {#section-model}

<a id="tag-XMYD" data-assertion="definition" data-title="Hierarchical lattice"></a><p>The vertex group is</p>
      $$\mathbb H_L^d=\bigoplus_{i\ge1}(\mathbb Z/L\mathbb Z)^d.$$
      <a id="tag-T6SL" data-assertion="definition" data-title="Hierarchical distance and ball volume"></a><p>Vertices are sequences with only finitely many nonzero coordinates. For $x\ne y$, their distance is $L^{\max\{i:x_i\ne y_i\}}$, and the distance from a vertex to itself is zero. A radius-$L^n$ ball contains $L^{dn}$ vertices.</p>
      <a id="tag-JCRB" data-assertion="definition" data-title="Smallest common hierarchical ball and regularized distance"></a><p>For vertices $x,y$, let $\Lambda(x,y)$ be the smallest hierarchical ball containing them, and put $\langle x-y\rangle=\max\{1,\|x-y\|\}$. A radial kernel depends only on this distance.</p><p>The <a href="#/product-model">independent intensity law</a> assigns an edge probability determined by its kernel value and the intensity parameter.</p>

## The critical estimate {#section-statement}

<a id="tag-W498" data-assertion="theorem" data-title="Critical pointwise two-point estimate for radial kernels"></a><div class="theorem-statement"><p>Let $0&lt;\alpha&lt;d$, and suppose that there are constants $c,C&gt;0$ such that</p>
      $$c\|x\|^{-d-\alpha}\le J(x)\le C\|x\|^{-d-\alpha}
      \qquad(x\ne0).$$
      <p>Then the <a href="#/criticality">critical intensity</a> satisfies $0&lt;\beta_c&lt;\infty$, and there are constants $a,A&gt;0$, depending only on $d,L,\alpha,c,C$, such that, for every $x,y\in\mathbb H_L^d$,</p>
      $$a\langle x-y\rangle^{-d+\alpha}
      \le \mathbb P_{\beta_c}\bigl(x\leftrightarrow y\text{ inside }\Lambda(x,y)\bigr)
      \le \mathbb P_{\beta_c}(x\leftrightarrow y)
      \le A\langle x-y\rangle^{-d+\alpha}.$$</div>
      <p>The lower bound already holds with <a href="#/connectivity">paths restricted to one ball</a>. The upper bound permits paths in the entire lattice. Radiality matters for this pointwise formulation; an averaged estimate under weaker symmetry belongs in a separate statement.</p>

## A ball susceptibility calculation {#section-consequence}

<a id="tag-V4QQ" data-assertion="corollary" data-title="Full-cluster susceptibility in a hierarchical ball"></a><p>The pointwise estimate immediately determines the <a href="#/susceptibility">finite-region susceptibility</a>, namely the expected mass of the full cluster inside a ball. The shell at distance $L^k$ contains $L^{dk}-L^{d(k-1)}$ vertices. Multiplying by a connection probability of order $L^{-k(d-\alpha)}$ gives a shell contribution of order $L^{\alpha k}$. Summing the geometric series yields</p>
      $$\mathbb E_{\beta_c}|K_0\cap\Lambda_n|
        =\sum_{x\in\Lambda_n}\mathbb P_{\beta_c}(0\leftrightarrow x)
        \asymp L^{\alpha n}.$$
      <a id="tag-YWTU" data-assertion="corollary" data-title="Restricted-cluster susceptibility in a hierarchical ball"></a><p>The restricted lower estimate also gives the same order for the cluster formed using only edges inside $\Lambda_n$. These are distinct observables with matching orders in this theorem.</p>

## Symmetry and further estimates {#section-position}

<p>Radial symmetry makes vertices on the same shell equivalent, relating averaged connection estimates to pointwise bounds. Critical estimates combine this multiscale geometry with general tools such as <a href="#/sharpness">sharpness</a> and <a href="#/universal-tightness">cluster tightness</a>.</p>
      <p>The spatial estimate supplies an input to <a href="#/triangle-condition">triangle-diagram calculations</a>. Cluster-volume tails, finite-size scaling, and statements at a marginal exponent need their own hypotheses and proofs; they should not be silently attached to this result.</p>

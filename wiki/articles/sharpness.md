---
{
  "id": "sharpness",
  "title": "Sharpness of the phase transition",
  "subtitle": "From a local certificate to the whole subcritical regime.",
  "kind": "theorem",
  "category": "Phase transition",
  "summary": "The elementary path bound finds a region of finite susceptibility. Sharpness identifies the entire subcritical region, and supplies a quantitative lower bound above the threshold.",
  "context": [
    "The lattice model is independent nearest-neighbour bond percolation on $\\mathbb Z^d$, with $d\\ge2$.",
    "The parameter p is the common edge-opening probability; p_c is the infinite-cluster threshold.",
    "The weighted long-range extension uses an intensity parameter β and states its own hypotheses."
  ],
  "related": [
    "subcritical-bound",
    "triangle-condition",
    "hierarchical-two-point"
  ],
  "sourceIds": [
    "dct-sharpness",
    "grimmett",
    "notes"
  ],
  "aliases": [
    "sharp phase transition",
    "finite-size criterion",
    "finite-set criterion",
    "Duminil-Copin–Tassion",
    "subcritical exponential decay"
  ],
  "prototypeUses": [
    "product-model",
    "connectivity",
    "susceptibility",
    "criticality",
    "exploration"
  ]
}
---

## A precise lattice statement {#section-statement}

<a id="tag-6THJ" data-assertion="theorem" data-title="Lattice sharpness and subcritical exponential decay"></a><div class="theorem-statement"><p>For the lattice model, let $p&lt;p_c$. Then the <a href="#/susceptibility">susceptibility</a> is finite:</p>
      $$\chi(p)=\mathbb E_p|K_0|&lt;\infty.$$
      <p>Moreover, there are constants $c_p,C_p&gt;0$ such that</p>
      $$\mathbb P_p\bigl(0\leftrightarrow \mathbb Z^d\setminus[-n,n]^d\bigr)\le C_p e^{-c_p n}\qquad(n\ge1).$$</div>
      <p>This advances the <a href="#/subcritical-bound">small-parameter estimate</a>: the condition is now $p&lt;p_c$, rather than an explicit but generally nonoptimal bound on the row sum.</p>

## The finite-set certificate {#section-certificate}

<a id="tag-6EIM" data-assertion="definition" data-title="Expected open boundary influence"></a><p>For a finite set $S\ni0$, define the expected open boundary influence</p>
      $$\varphi_p(S)=p\!\!\sum_{\substack{x\in S,\;y\notin S\\x\sim y}}\mathbb P_p(0\leftrightarrow x\text{ inside }S).$$
      <p>The probability in the definition uses <a href="#/connectivity">connectivity restricted to the set</a>. The useful certificate is $\varphi_p(S)&lt;1$. It says that an <a href="#/exploration">exploration</a> reaching the boundary of this region produces less than one unit of expected outgoing influence. A decomposition at successive exits turns the certificate into decay estimates. Taking $S=\{0\}$ recovers the simple criterion $2dp&lt;1$; larger sets account for the connections already formed inside a region.</p>
      <a id="tag-FCU7" data-assertion="theorem" data-title="Subcritical finite-set certificate"></a><p>The deeper step is to prove that a certificate exists for every $p&lt;p_c$. The proof combines a differential inequality with a boundary exploration, identifying the threshold defined by finite certificates with the threshold defined by infinite clusters.</p>

## What survives for long-range percolation {#section-long-range}

<a id="tag-DYUM" data-assertion="theorem" data-title="Sharpness for summable long-range intensity kernels"></a><p>Consider instead the <a href="#/product-model">intensity law</a> $q_\beta(x,y)=1-e^{-\beta J(y-x)}$ on $\mathbb Z^d$, with a nonnegative symmetric, translation-invariant kernel satisfying $\sum_{x\ne0}J(x)&lt;\infty$. Suppose its threshold satisfies $0&lt;\beta_c&lt;\infty$. The sharpness theorem yields</p>
      $$\chi(\beta)&lt;\infty\quad(\beta&lt;\beta_c),\qquad
      \theta(\beta)\ge \frac{\beta-\beta_c}{\beta}\quad(\beta&gt;\beta_c).$$
      <p>The susceptibility conclusion applies even when the interaction has infinite range. Exponential decay in Euclidean distance requires additional assumptions: a single long open edge already gives a lower bound on distant connectivity. For a power-law kernel, that lower bound is itself polynomial.</p>

## Proof ingredients and scope {#section-route}

<p>The argument combines finite-volume differentiation, boundary exploration, monotonicity, and passage to infinite volume. The final geometric decay statement adds a finite-range argument. The susceptibility argument extends to infinite-range interactions even when that final geometric argument does not.</p>
      <p>Sharpness does not by itself decide whether there is an infinite cluster exactly at the threshold. Behaviour at the <a href="#/criticality">critical threshold</a> is an additional question. The <a href="#/triangle-condition">triangle condition</a> is a stronger hypothesis yielding quantitative cluster-volume estimates at criticality.</p>

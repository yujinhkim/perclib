---
{
  "id": "window-tightness-interfaces",
  "title": "Finite-window tightness interfaces",
  "subtitle": "Quantile targets, amplification and the excluded zero iteration",
  "kind": "method",
  "category": "Cluster geometry",
  "summary": "The library records universal quantile bounds and a finite-window amplification property as proof targets. Their scope includes arbitrary Bernoulli profiles, outside roots and full-cluster intersections.",
  "context": ["A countable vertex set V with an arbitrary independent unordered-pair profile, including probabilities zero and one.", "A finite nonempty observation set; clusters are formed in the whole graph and the distinguished root need not belong to the observation set.", "The two properties below specify targets. The inspected source defines them but does not prove that all countable vertex sets satisfy them."],
  "related": ["universal-tightness", "cluster-partitions", "finite-volume", "bk-inequality"],
  "sourceIds": ["perclib-tightness-interface", "hutchcroft-powerlaw-2021"],
  "aliases": ["tightness target", "finite-window amplification", "quantile endpoint", "marked tree splitting"],
  "prototypeUses": []
}
---

## The observed quantities {#section-observables}

<p>Use the <a href="/tag/GJIW/">maximum cluster intersection and quantile</a>, now for an arbitrary Bernoulli profile $q$. Write</p>
<div class="math-display">$$X=\max_{v\in\Lambda}|K_v\cap\Lambda|,\qquad Y_u=|K_u\cap\Lambda|,\qquad M=\min\{n\in\mathbb N:\mathbb P_q(X\geq n)\leq e^{-1}\}.$$</div>
<p>These are full-cluster intersections. An open path between two observed vertices may leave $\Lambda$, and $u$ may lie outside $\Lambda$. Since $1\leq X\leq|\Lambda|$, the integer minimum exists and $2\leq M\leq|\Lambda|+1$. Allowing zero in its defining set changes nothing: the tail at zero is one. Connection measurability on countable vertex sets makes each finite intersection count and its maximum measurable.</p>
<p>For a singleton $\Lambda=\{v\}$, one has $X=1$ in every configuration, hence $M=2$ for every profile. Indeed, the tails at zero and one are one, and the tail at two is zero. For an outside root, $Y_u$ is instead the indicator that $u$ connects to $v$; it need not be identically one. Thus the singleton witness tests the maximum and quantile conventions without collapsing the rooted observable.</p>

## Two properties to prove {#section-properties}

<a id="tag-C5Q9" data-assertion="definition" data-title="Universal quantile-tail property on a countable vertex set"></a>
<p>A countable vertex set has the <em>universal quantile-tail property</em> if, for every independent pair profile $q$, finite nonempty $\Lambda$, real $a\geq1$, real $0&lt;\varepsilon\leq1$, and root $u$,</p>
<div class="math-display">$$\mathbb P_q(X\geq aM)\leq e^{-a/9},\qquad \mathbb P_q(X&lt;\varepsilon M)\leq27\varepsilon,$$</div>
<div class="math-display">$$\mathbb P_q(Y_u\geq aM)\leq e\,\mathbb P_q(Y_u\geq M)e^{-a/9}.$$</div>
<p>This is the general-profile target corresponding to the <a href="/tag/4724/">two-sided quantile bounds</a> and <a href="/tag/21D4/">rooted refinement</a>. The source paper states the weighted exponential model; the library target explicitly ranges over all profiles, including probability-one coordinates. The formulas retain the non-strict upper tails and the strict lower-tail event.</p>

<a id="tag-JGZB" data-assertion="definition" data-title="Finite-window amplification property with at least one iteration"></a>
<p>A countable vertex set has the <em>finite-window amplification property</em> if, for every profile $q$, finite nonempty $\Lambda$, real $\lambda\geq1$, integer $k\geq1$, and root $u$,</p>
<div class="math-display">$$\mathbb P_q(X\geq3^k\lambda)\leq\mathbb P_q(X\geq\lambda)^{3^{k-1}+1},$$</div>
<div class="math-display">$$\mathbb P_q(Y_u\geq3^k\lambda)\leq\mathbb P_q(X\geq\lambda)^{3^{k-1}}\mathbb P_q(Y_u\geq\lambda).$$</div>
<p>The exponent $k-1$ is an ordinary nonnegative integer because $k\geq1$. This is the corrected range used by the library target, following the source discrepancy recorded in <a href="https://github.com/tomhutchcroft/lrp/issues/52">issue 52</a>. It is not a claim that the paper prints that range, or that Tom has resolved the reserved source-fidelity decision.</p>
<p>These definitions package the statements to be established. They are not proofs of universal tightness or amplification. The pinned source contains the two proposition definitions and the singleton identities above, but no proof of either universal property. Nor does this article assert a compiled tag association for them.</p>

## Why zero iterations must be excluded {#section-zero}

<p>Take two vertices joined by one bond of probability $1/2$, let $\Lambda$ contain both vertices and set $\lambda=2$. Then $X$ is two when the bond is open and one when it is closed, so $\mathbb P(X\geq2)=1/2$. At $k=0$, the first proposed inequality with the printed real exponent would give</p>
<div class="math-display">$$\frac12\leq\left(\frac12\right)^{4/3},$$</div>
<p>which is false. Interpreting $k-1$ as truncated natural subtraction would instead give exponent two and is false as well. Choosing either endpoint as $u$ gives the same counterexample to the rooted inequality: its two tail factors again multiply to $(1/2)^{4/3}$, or to $1/4$ with truncated subtraction. Restricting to $k\geq1$ removes this false endpoint; it does not by itself prove the remaining inequalities.</p>

## What the proof still needs {#section-obligations}

<p>The amplification route first partitions a finite connected witness into connected edge pieces with controlled numbers of marked vertices. Pairwise disjoint edge sets are essential for <a href="/tag/AUUG/">repeated BK</a>, and the pieces must cover the original edges and retain coverage of the distinguished root, including when it lies outside $\Lambda$. Merely finding several connected subgraphs, or making their vertex sets disjoint, is a different assertion.</p>
<p>Once the finite amplification inequalities are available, their fixed-threshold events pass to a countable host through finite-edge approximations and finite connectivity witnesses. This passage uses convergence of probabilities and finite powers; it does not require continuity of the integer quantile $M$. The quantile estimates then need a separate numerical argument. These steps identify the remaining proof obligations rather than treating a source citation or a target definition as their discharge.</p>

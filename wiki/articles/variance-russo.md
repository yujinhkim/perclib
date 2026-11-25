---
{
  "id": "variance-russo",
  "title": "Variance and elementary derivative bounds",
  "subtitle": "Finite-product tensorization and an integrated Russo bound",
  "kind": "theorem",
  "category": "Foundations",
  "summary": "An elementary variance inequality controls a finite increasing event by its pivotal coordinates and yields an odds comparison across parameters.",
  "context": ["A finite set $E$ of independent Bernoulli coordinates.", "A real observable $f$; increasingness is imposed only for the event derivative bound.", "Homogeneous parameters lie in $(0,1)$ when division or logarithms are used."],
  "related": ["russo-formula", "harris-inequality", "product-model"],
  "sourceIds": ["notes", "perclib-elementary-square"],
  "aliases": ["variance tensorization", "Bernoulli Poincare inequality", "elementary threshold bound", "odds comparison"],
  "prototypeUses": ["russo-formula"]
}
---

## Variance tensorization {#section-variance}

<a id="tag-R428" data-assertion="theorem" data-title="Variance tensorization for finite Bernoulli products"></a>
<p>For a finite set $E$, a profile $q\in[0,1]^E$ and any $f:\{0,1\}^E\to\mathbb R$,</p>
<div class="math-display">$$\operatorname{Var}_q(f)\leq\sum_{e\in E}q_e(1-q_e)\,\mathbb E_q[(\Delta_e f)^2],$$</div>
<p>where $\Delta_e f$ is the forced-coordinate increment of <a href="/tag/71GK/">71GK</a>. Probabilities zero and one are allowed. For an empty coordinate set both sides vanish.</p>
<p><em>Proof.</em> Induct on $|E|$. Choose $e\in E$ and write $g$ for the average of $f$ over coordinate $e$, regarded as a function of the remaining coordinates. The variance decomposition gives</p>
<div class="math-display">$$\operatorname{Var}_q(f)=q_e(1-q_e)\mathbb E_q[(\Delta_e f)^2]+\operatorname{Var}_{q|_{E\setminus\{e\}}}(g).$$</div>
<p>Apply the induction hypothesis to $g$. For each $i\ne e$, averaging over $e$ commutes with taking $\Delta_i$, so Jensen's inequality gives $(\Delta_i g)^2\leq\mathbb E_e[(\Delta_i f)^2]$. Integration over the other coordinates bounds its contribution by $q_i(1-q_i)\mathbb E_q[(\Delta_i f)^2]$. Summing proves the claim. All averages are finite sums, so degenerate coordinates cause no conditioning difficulty.</p>
<p>The scalar estimate behind the convexity step is elementary: for real $a,b$, $2ab\leq a^2+b^2$ because $(a-b)^2\geq0$. More precisely, for $t\in[0,1]$,</p>
<div class="math-display">$$ta^2+(1-t)b^2-(ta+(1-t)b)^2=t(1-t)(a-b)^2\geq0.$$</div>
<p>This proves the two-point Jensen inequality used when averaging a Bernoulli coordinate, including $t=0$ and $t=1$.</p>
<p>The inequality is exact for a single coordinate. For a general event $A$, the squared increment of $\mathbf1_A$ records whether changing the coordinate changes membership, regardless of direction. Replacing this square by the signed increment is valid for increasing events, but not for arbitrary events.</p>

## A derivative bound for increasing events {#section-derivative}

<a id="tag-GI8Q" data-assertion="corollary" data-title="Elementary finite-event derivative inequality"></a>
<p>Let $A\subseteq\{0,1\}^E$ be increasing and let $F(p)=\mathbb P_p(A)$ under the homogeneous Bernoulli law. For $0&lt;p&lt;1$,</p>
<div class="math-display">$$p(1-p)F'(p)\geq F(p)(1-F(p)).$$</div>
<p><em>Proof.</em> Increasingness gives $(\Delta_e\mathbf1_A)^2=\Delta_e\mathbf1_A=\mathbf1_{\{e\text{ pivotal}\}}$. Apply variance tensorization to $\mathbf1_A$ and use the finite homogeneous Russo formula <a href="/tag/4IHK/">4IHK</a> to identify the sum of pivotal probabilities with $F'(p)$.</p>
<p>Both constant events satisfy the inequality, with both sides zero. At $p=0$ and $p=1$, the polynomial extension also satisfies the displayed inequality with both sides zero; these endpoint identities cannot be divided by $p(1-p)$.</p>

## Integrated odds {#section-odds}

<a id="tag-6ITM" data-assertion="corollary" data-title="Odds comparison for a nonconstant increasing finite event"></a>
<p>Suppose $A$ is increasing, nonempty and not the whole configuration space. For $0&lt;a&lt;b&lt;1$,</p>
<div class="math-display">$$\frac{F(b)}{1-F(b)}\geq\frac{F(a)}{1-F(a)}\frac{b(1-a)}{a(1-b)}.$$</div>
<p>Equivalently, $F(p)/(1-F(p))$ divided by $p/(1-p)$ is nondecreasing on $(0,1)$. In particular, writing $u=F(a)$ gives</p>
<div class="math-display">$$F(b)\geq\frac{u\,b(1-a)}{u\,b(1-a)+(1-u)a(1-b)}.$$</div>
<p><em>Proof.</em> Every configuration has positive probability for $0&lt;p&lt;1$. The assumptions on $A$ therefore imply $0&lt;F(p)&lt;1$. Divide the derivative inequality by $p(1-p)F(p)(1-F(p))$ to obtain</p>
<div class="math-display">$$\frac{d}{dp}\log\frac{F(p)}{1-F(p)}\geq\frac1{p(1-p)}=\frac{d}{dp}\log\frac p{1-p}.$$</div>
<p>Integration from $a$ to $b$ and exponentiation give the odds comparison; solving it for $F(b)$ gives the final expression.</p>
<p>For $A=\{X_e=1\}$, one has $F(p)=p$ and equality throughout. This example also shows the limitation of the estimate: by itself it does not force a narrowing transition window as the number of available coordinates grows, since an event may ignore all but one coordinate.</p>

## Place in the source argument {#section-scope}

<p>This is a finite-product auxiliary to the Russo and decision-tree methods discussed in Chapters 4 and 6 of the preliminary notes. It is not asserted to be a source occurrence of their OSSS proposition. The variance estimate charges every coordinate with its full contribution; an algorithmic inequality can improve this by exploiting small revealment, but requires its own theorem and hypotheses.</p>
<p>The argument does not justify differentiating an infinite-volume percolation probability or prove sharpness of the infinite-volume phase transition. Passing to a limiting event needs an additional argument, even though each finite-coordinate approximation satisfies the inequalities above.</p>

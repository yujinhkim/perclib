---
{
  "id": "ordered-product-association",
  "title": "Association on ordered product spaces",
  "subtitle": "Coordinate averaging without an enumeration",
  "kind": "theorem",
  "category": "Foundations",
  "summary": "Increasing measurable events are positively associated under products of linearly ordered probability spaces. Finite-coordinate averaging proves the result for arbitrary index sets.",
  "context": ["An arbitrary index set $I$ and probability spaces $(X_i,\\mathcal F_i,\\mu_i)$.", "The product sigma-algebra on $X=\\prod_i X_i$ and product law $\\mu=\\bigotimes_i\\mu_i$.", "For association, each $X_i$ is linearly ordered and $X$ carries the coordinatewise order; measurability of observables is assumed separately."],
  "related": ["harris-inequality", "product-model", "finite-transcripts", "profile-continuity"],
  "sourceIds": ["perclib-ordered-harris"],
  "aliases": ["Chebyshev integral inequality", "product association", "finite-coordinate averaging", "cylinder approximation"],
  "prototypeUses": []
}
---

## One ordered coordinate {#section-one-coordinate}

<a id="tag-P52U" data-assertion="proposition" data-title="Chebyshev integral inequality on a linearly ordered probability space"></a>
<p>Let $\nu$ be a probability measure on a linearly ordered measurable space $Y$. If $f,g:Y\to\mathbb R$ are bounded, measurable and increasing, then</p>
<div class="math-display">$$\left(\int f\,d\nu\right)\left(\int g\,d\nu\right)\leq\int fg\,d\nu.$$</div>
<p><em>Proof.</em> For any $x,y\in Y$, the two differences $f(x)-f(y)$ and $g(x)-g(y)$ have the same sign, since either $x\leq y$ or $y\leq x$. Hence</p>
<div class="math-display">$$0\leq\iint(f(x)-f(y))(g(x)-g(y))\,d\nu(x)d\nu(y)=2\left(\int fg\,d\nu-\int f\,d\nu\int g\,d\nu\right).$$</div>
<p>Boundedness justifies expansion and Fubini. No compatibility between the order and sigma-algebra is needed beyond the stated measurability of $f$ and $g$.</p>

## Averaging the unobserved coordinates {#section-averaging}

<p>For finite $F\subseteq I$, write $x_Fy$ for the configuration taking its coordinates in $F$ from $x$ and all others from $y$. For a bounded measurable real function $f$, define</p>
<div class="math-display">$$T_F f(x)=\int f(x_Fy)\,d\mu(y).$$</div>

<a id="tag-WBBE" data-assertion="proposition" data-title="Finite-coordinate averaging preserves means and contracts differences"></a>
<p>The splicing map $(x,y)\mapsto x_Fy$ is measurable and sends $\mu\otimes\mu$ to $\mu$. The function $T_Ff$ is measurable, depends only on the coordinates in $F$, and satisfies</p>
<div class="math-display">$$\int T_Ff\,d\mu=\int f\,d\mu,\qquad \|T_Ff\|_\infty\leq\|f\|_\infty.$$</div>
<p>Here the sup norm can be taken as the pointwise bound. If $f$ depends only on $F$, then $T_Ff=f$ pointwise. For bounded measurable $f,g$,</p>
<div class="math-display">$$\|T_Ff-T_Fg\|_{L^1(\mu)}\leq\|f-g\|_{L^1(\mu)}.$$</div>
<p>If each coordinate has a preorder and $f$ is increasing, then $T_Ff$ is increasing. For a merely integrable measurable $f$, the spliced integrand is integrable on the product space, its sections are integrable for almost every $x$, and the mean identity still holds for the almost-everywhere defined section integral.</p>
<p><em>Proof.</em> Each coordinate of the splicing map is a coordinate projection. The image of two independent product samples has the correct finite-coordinate distributions: coordinates in $F$ come from the first sample, the others from the second, and all are independent with the specified marginals. Uniqueness on the cylinder pi-system identifies its law as $\mu$.</p>
<p>Measurability of the section integral and the mean identity follow from Fubini and this pushforward identity. Boundedness gives integrable sections at every $x$, as well as the sup bound. The spliced configuration uses $x$ only on $F$, so the average does too; if $f$ reads only $F$, its integrand is constantly $f(x)$. For the contraction, use</p>
<div class="math-display">$$|T_Ff(x)-T_Fg(x)|\leq\int |f(x_Fy)-g(x_Fy)|\,d\mu(y)$$</div>
<p>and integrate in $x$. The pushforward identity turns the right side into $\|f-g\|_1$. If $x\leq x'$, then $x_Fy\leq x'_Fy$ for every $y$, which proves monotonicity of the average. Finally, for integrable $f$, the same pushforward identity gives</p>
<div class="math-display">$$\iint |f(x_Fy)|\,d\mu(y)d\mu(x)=\int |f|\,d\mu&lt;\infty;$$</div>
<p>Fubini supplies the asserted almost-everywhere section integrability and mean identity.</p>

## Approximation by finite observations {#section-approximation}

<a id="tag-NPRG" data-assertion="proposition" data-title="Finite-coordinate averages approximate measurable indicators in L1"></a>
<p>For every measurable $A\subseteq X$ and every $\varepsilon&gt;0$, there is a finite $F_0\subseteq I$ such that every finite $F\supseteq F_0$ satisfies</p>
<div class="math-display">$$\|T_F\mathbf1_A-\mathbf1_A\|_{L^1(\mu)}&lt;\varepsilon.$$</div>
<p><em>Proof.</em> Every measurable event can be approximated in measure by an event depending on finitely many coordinates. To see this, let $\mathcal D$ consist of events with that approximation property. It contains the finite-coordinate algebra and is closed under complements and finite unions. If $A_n\in\mathcal D$, first approximate $\bigcup_n A_n$ by a finite partial union using continuity of the finite measure from below, then approximate that finite union by finite-coordinate events. Thus $\mathcal D$ is a sigma-algebra containing the generators of the product sigma-algebra.</p>
<p>Choose a measurable finite-coordinate event $C$ with $\mu(A\mathbin\triangle C)&lt;\varepsilon/2$, and let $F_0$ contain its coordinates. For $F\supseteq F_0$, the preceding proposition gives $T_F\mathbf1_C=\mathbf1_C$ and</p>
<div class="math-display">$$\|T_F\mathbf1_A-\mathbf1_A\|_1\leq\|T_F(\mathbf1_A-\mathbf1_C)\|_1+\|\mathbf1_C-\mathbf1_A\|_1\leq2\mu(A\mathbin\triangle C)&lt;\varepsilon.$$</div>
<p>The quantifier is over all finite supersets of $F_0$. No enumeration of $I$, and no countability assumption on it, has been used.</p>

## Positive association {#section-association}

<a id="tag-9U6I" data-assertion="theorem" data-title="Harris association for products of linearly ordered probability spaces"></a>
<p>Suppose each $X_i$ is linearly ordered. Bounded increasing measurable real functions $f,g$ depending on finitely many coordinates satisfy</p>
<div class="math-display">$$\int f\,d\mu\int g\,d\mu\leq\int fg\,d\mu.$$</div>
<p>For any increasing measurable events $A,B\subseteq X$, without a finite-dependence assumption,</p>
<div class="math-display">$$\mu(A)\mu(B)\leq\mu(A\cap B).$$</div>
<p><em>Proof.</em> For finite-coordinate functions, induct on the size of a finite set containing both dependencies. With no coordinates both functions are constant. Otherwise fix one coordinate value and apply the induction hypothesis to the remaining coordinates. Their averages are bounded measurable increasing functions of the fixed coordinate. The one-coordinate inequality then bounds the average of their product below by the product of their averages, proving the induction step.</p>
<p>For general events, let $a=\mathbf1_A$ and $b=\mathbf1_B$. Their finite-coordinate averages are increasing, take values in $[0,1]$ and have means $\mu(A)$ and $\mu(B)$. The finite-coordinate inequality gives</p>
<div class="math-display">$$\mu(A)\mu(B)\leq\int (T_Fa)(T_Fb)\,d\mu.$$</div>
<p>Given $\varepsilon&gt;0$, the approximation lemma supplies a common finite $F$ for which both $L^1$ errors are below $\varepsilon$. Since the four functions take values in $[0,1]$,</p>
<div class="math-display">$$\left|\int(T_Fa)(T_Fb)\,d\mu-\int ab\,d\mu\right|\leq\|T_Fa-a\|_1+\|T_Fb-b\|_1&lt;2\varepsilon.$$</div>
<p>Let $\varepsilon\downarrow0$. The limit on the right is $\mu(A\cap B)$, as required.</p>
<p>The Bernoulli case is the <a href="/tag/X5SS/">Harris inequality</a>, obtained with $X_i=\{0,1\}$. The theorem does not require finite open witnesses. For example, on countably many Bernoulli coordinates, the event that every coordinate is open is measurable and increasing, but no finite set of open coordinates certifies it. Nor does positive association mean independence: taking $A=B$ gives an inequality that is strict whenever $0&lt;\mu(A)&lt;1$.</p>

---
{
  "id": "regular-variation",
  "title": "Regular variation and Laplace tails",
  "subtitle": "Exact constants, tail order and the limits of local conclusions",
  "kind": "method",
  "category": "Methods",
  "summary": "Karamata's Laplace–tail theorem fixes the Gamma normalization in the passage from cluster-size tails to magnetization. Tail equivalents do not imply all-integer point-mass equivalents.",
  "context": ["A nonnegative random variable $X$ that is finite almost surely.", "The transform is $M_X(h)=\\mathbb E[1-e^{-hX}]$ for $h>0$.", "The fractional tail index satisfies $0<\\alpha<1$."],
  "related": ["ghost-fields", "branching-processes", "binary-tree-percolation", "susceptibility"],
  "sourceIds": ["notes"],
  "aliases": ["Karamata", "Tauberian", "slowly varying", "regular variation", "Laplace", "Gamma constant"],
  "prototypeUses": []
}
---

## Regular variation {#section-definition}

<a id="tag-3491" data-assertion="definition" data-title="Slow and regular variation at infinity"></a><p>A positive measurable function $L$ is slowly varying at infinity if $L(\lambda x)/L(x)\to1$ for every fixed $\lambda&gt;0$. A positive measurable function $f$ is regularly varying with index $\rho$ if $f(x)=x^\rho L(x)$ for such an $L$; equivalently, $f(\lambda x)/f(x)\to\lambda^\rho$ for every fixed $\lambda&gt;0$.</p><p>Powers of $\log x$ and $\log\log x$, restricted to sufficiently large $x$, are slowly varying. Thus $x^{-\alpha}(\log x)^a$ has index $-\alpha$, even though its ratio to $x^{-\alpha}$ need not approach a positive constant.</p>

## The transform normalization {#section-normalization}

<a id="tag-LTJ1" data-assertion="proposition" data-title="Continuous tail integral for the Laplace deficit"></a><p>For every $h&gt;0$,</p><div class="math-display">$$M_X(h)=h\int_0^\infty e^{-ht}\mathbb P(X&gt;t)\,dt=\int_0^\infty e^{-u}\mathbb P(X&gt;u/h)\,du.$$</div><p><em>Proof.</em> Integrate $he^{-ht}$ from zero to $X$, then apply Tonelli's theorem to the nonnegative integrand. The second equality is the change of variables $u=ht$.</p><p>This identity fixes the convention: the transform is the deficit $1-\mathbb E[e^{-hX}]$, not the Laplace transform of a density. For integer-valued $X$, the same identity holds with its step-function tail. The discrete version is the <a href="#/ghost-fields">geometric tail sum</a>.</p>

## The Laplace–tail theorem {#section-karamata}

<a id="tag-SLGY" data-assertion="theorem" data-title="Karamata Laplace–tail equivalence for fractional index"></a><p>Let $0&lt;\alpha&lt;1$ and let $L$ be positive, measurable and slowly varying at infinity. Then</p><div class="math-display">$$\mathbb P(X&gt;t)\sim t^{-\alpha}L(t)\quad(t\to\infty)$$</div><p>if and only if</p><div class="math-display">$$M_X(h)\sim\Gamma(1-\alpha)h^\alpha L(1/h)\quad(h\downarrow0).$$</div><p>This is the classical Karamata Laplace–tail theorem. Both directions are proved below. The tail is automatically nonincreasing, and no point-mass asymptotic is included.</p><p>The normalization is determined by</p><div class="math-display">$$\int_0^\infty e^{-u}u^{-\alpha}\,du=\Gamma(1-\alpha).$$</div><p><em>Proof of the forward implication.</em> Write $F(t)=\mathbb P(X&gt;t)$ and $x=1/h$. The tail assumption gives $F(ux)/F(x)\to u^{-\alpha}$ for every $u&gt;0$. We need an integrable bound to pass to the limit in</p>
<div class="math-display">$$\frac{M_X(1/x)}{F(x)}=\int_0^\infty e^{-u}\frac{F(ux)}{F(x)}\,du.$$</div>
<p>Choose $0&lt;\varepsilon&lt;\min\{\alpha,1-\alpha\}$. Since $F(2t)/F(t)\to2^{-\alpha}$, there is $x_0&gt;0$ such that $F(t)&gt;0$ and</p>
<div class="math-display">$$2^{-\alpha-\varepsilon}\leq\frac{F(2t)}{F(t)}\leq2^{-\alpha+\varepsilon}\qquad(t\geq x_0).$$</div>
<p>Iteration on dyadic scales, together with monotonicity of $F$, gives a constant $C$ such that, whenever $x\geq x_0$ and $ux\geq x_0$,</p>
<div class="math-display">$$\frac{F(ux)}{F(x)}\leq C\begin{cases}u^{-\alpha-\varepsilon},&amp;0&lt;u\leq1,\\u^{-\alpha+\varepsilon},&amp;u\geq1.\end{cases}$$</div>
<p>Indeed, for $u\geq1$ iterate the upper ratio bound from $x$ to the last dyadic point below $ux$. For $u\leq1$, iterate the lower bound from $ux$ to the first dyadic point at or above $x$, then use monotonicity there. The same lower bound, iterated from $x_0$, shows $xF(x)\to\infty$: on $2^kx_0\leq x&lt;2^{k+1}x_0$,</p>
<div class="math-display">$$xF(x)\geq2^kx_0F(2^{k+1}x_0)\geq x_0F(x_0)\,2^{-\alpha-\varepsilon}\,2^{k(1-\alpha-\varepsilon)}\longrightarrow\infty.$$</div>
<p>The part of the integral with $ux&lt;x_0$ is at most $x_0/(xF(x))$, which tends to zero. On the remaining part, the displayed bound times $e^{-u}$ is integrable: $\alpha+\varepsilon&lt;1$ controls zero and the exponential controls infinity. Dominated convergence now gives</p>
<div class="math-display">$$\frac{M_X(1/x)}{F(x)}\longrightarrow\int_0^\infty e^{-u}u^{-\alpha}\,du=\Gamma(1-\alpha).$$</div>
<p>Substituting $F(x)\sim x^{-\alpha}L(x)$ proves the claimed transform asymptotic.</p>
<p><em>Proof of the converse.</em> Suppose the transform has the stated asymptotic, and put $a(x)=x^{-\alpha}L(x)$. Define finite measures on $[0,\infty)$ by</p>
<div class="math-display">$$d\mu_x(u)=e^{-u}\frac{F(xu)}{a(x)}\,du,\qquad d\mu(u)=e^{-u}u^{-\alpha}\,du.$$</div>
<p>For each integer $n\geq0$, the tail integral and slow variation give</p>
<div class="math-display">$$\int_0^\infty e^{-nu}\,d\mu_x(u)=\frac{M_X((n+1)/x)}{(n+1)a(x)}\longrightarrow\Gamma(1-\alpha)(n+1)^{\alpha-1}=\int_0^\infty e^{-nu}\,d\mu(u).$$</div>
<p>Push these measures forward by $z=e^{-u}$ to $[0,1]$. The displayed limits give convergence of every polynomial moment, including the total mass at $n=0$. Uniform polynomial approximation on $[0,1]$ therefore gives convergence of integrals of every continuous function. The limit measure has no atoms. For $0&lt;r&lt;s&lt;\infty$, we may consequently also integrate the bounded function $z^{-1}\mathbf1_{[e^{-s},e^{-r}]}(z)$, defined to be zero outside that interval: approximate it by continuous functions across its two endpoints. Undoing the change of variables yields</p>
<div class="math-display">$$\int_r^s\frac{F(xu)}{a(x)}\,du\longrightarrow\int_r^s u^{-\alpha}\,du.$$</div>
<p>Monotonicity of $F$ now recovers its value at $x$. For $0&lt;\delta&lt;1$,</p>
<div class="math-display">$$\frac1\delta\int_1^{1+\delta}\frac{F(xu)}{a(x)}\,du\leq\frac{F(x)}{a(x)}\leq\frac1\delta\int_{1-\delta}^1\frac{F(xu)}{a(x)}\,du.$$</div>
<p>Take the lower and upper limits as $x\to\infty$, then let $\delta\downarrow0$. Both bounding averages tend to one, so $F(x)\sim a(x)$, as required. This last step is where the monotonicity of the tail enters the converse.</p>
<p>The theorem justifies the limiting passage suggested by the preceding tail integral. For integer-valued $X$, one may equivalently write $\mathbb P(X\geq n)\sim n^{-\alpha}L(n)$; rounding the argument does not change a regularly varying tail or introduce an extra lattice factor in this transform.</p><p>The <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L607">notes quote this result as S002</a>, with an informal normalization and unspecified converse qualifications. The statement above fixes the transform, the range of the index, and the role of the monotone tail. The two-sided power-order equivalence proved in the <a href="#/ghost-fields">ghost-field article</a> is a different, weaker conclusion that needs no regular-variation assumption.</p>

## The critical progeny constant {#section-progeny}

<a id="tag-PVM9" data-assertion="corollary" data-title="Exact critical total-progeny tail constant"></a><p>For a Galton–Watson process started from one individual with offspring mean one and variance $0&lt;\sigma^2&lt;\infty$, its total progeny satisfies</p><div class="math-display">$$\mathbb P(T\geq n)\sim\sqrt{\frac{2}{\pi\sigma^2}}\,n^{-1/2}.$$</div><p><em>Proof.</em> Critical extinction gives $T&lt;\infty$ almost surely. The <a href="#/branching-processes">critical generating-function asymptotic</a> and $1-e^{-h}\sim h$ give $\mathbb E[1-e^{-hT}]\sim\sqrt{2/\sigma^2}\,h^{1/2}$. Apply the theorem with $\alpha=1/2$ and $\Gamma(1/2)=\sqrt\pi$.</p><p>For the critical rooted binary tree, $\sigma^2=1/2$, recovering the coefficient $2/\sqrt\pi$ obtained directly from the Catalan law. For offspring zero or two with equal probabilities, $\sigma^2=1$ and the tail equivalent still holds, although $\mathbb P(T=n)=0$ for every even $n$. A tail equivalent cannot be differentiated term by term to obtain an unrestricted local equivalent.</p>

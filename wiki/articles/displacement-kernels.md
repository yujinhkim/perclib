---
{
  "id": "displacement-kernels",
  "title": "Displacement kernels and translation symmetry",
  "subtitle": "Unordered pairs, the choice of translation action, and exact row sums",
  "kind": "model",
  "category": "Models",
  "summary": "An inversion-even displacement kernel defines symmetric pair intensities. Its off-diagonal row is the kernel mass away from the identity, and the chosen displacement convention determines which translations preserve it.",
  "context": ["A countable group $G$ with identity $e$, written multiplicatively until the examples on additive groups.", "A finite nonnegative intensity kernel $k:G\\to[0,\\infty)$; its sum may be infinite.", "The convention $J(x,y)=k(yx^{-1})$ corresponds to $k(y-x)$ in additive notation."],
  "related": ["product-model", "product-symmetries", "subcritical-bound", "criticality", "hierarchical-two-point"],
  "sourceIds": ["notes", "perclib-translation-models"],
  "aliases": ["displacement kernel", "translation invariant", "even kernel", "right translation", "conjugacy invariant", "kernel row sum"],
  "prototypeUses": []
}
---

## Descending to unordered pairs {#section-symmetry}

<a id="tag-U8CI" data-assertion="proposition" data-title="Even displacement kernels and the translation action"></a><p>The prescription $J(x,y)=k(yx^{-1})$ defines a function on unordered pairs, including repeated pairs, if and only if</p><div class="math-display">$$k(z^{-1})=k(z)\qquad(z\in G).$$</div><p>When this holds, it is invariant under simultaneous right translation:</p><div class="math-display">$$J(xg,yg)=J(x,y).$$</div><p>It is invariant under all simultaneous left translations if and only if $k$ is conjugacy invariant, meaning $k(gzg^{-1})=k(z)$ for every $g,z\in G$.</p><p><em>Proof.</em> Swapping $x,y$ replaces $yx^{-1}$ by its inverse, so inversion symmetry is sufficient. Conversely, symmetry of the pair $(e,z)$ gives $k(z)=k(z^{-1})$. For right translations,</p><div class="math-display">$$(yg)(xg)^{-1}=yx^{-1},$$</div><p>whereas left translation changes the displacement to $(gy)(gx)^{-1}=g(yx^{-1})g^{-1}$. This proves sufficiency of conjugacy invariance; taking $x=e$ and $y=z$ proves necessity.</p><p>On an Abelian group, left and right translation coincide, and inversion symmetry is the usual condition $k(-z)=k(z)$. On a general group the distinction matters. For example, in the permutation group of three letters, the kernel supported on one transposition is inversion-even but not conjugacy invariant: conjugation can move that transposition to another one. The corresponding pair intensity is right-invariant but need not be left-invariant.</p><p>Using $k(x^{-1}y)$ instead would give the left-invariant convention. The two conventions agree on Abelian groups. A statement about translation symmetry should specify the action when the group is not Abelian.</p>

## The off-diagonal row {#section-row}

<a id="tag-R01V" data-assertion="proposition" data-title="Displacement-kernel row identity excluding the diagonal"></a><p>For $J(x,y)=k(yx^{-1})$, every vertex has the same off-diagonal row:</p><div class="math-display">$$\sum_{y\ne x}J(x,y)=\sum_{z\ne e}k(z)=:M\leq\sum_zk(z).$$</div><p>These are nonnegative extended sums. The identity does not need inversion symmetry; that condition is needed to interpret the ordered-pair expression as an undirected bond intensity. It is unchanged if the diagonal values $J(x,x)$ are replaced arbitrarily.</p><p><em>Proof.</em> The map $y\mapsto yx^{-1}$ is a bijection from $G$ to itself, taking $x$ to $e$. Reindex the sum over their complements. The inequality follows by adding the nonnegative identity term.</p><p>Thus a bound on the total kernel mass is sufficient, but it may discard useful information: $k(e)$ contributes to that total and not to any open edge of the simple graph. A positive kernel concentrated at the identity produces no non-loop bonds.</p>

## Probability profiles and intensity families {#section-probability}

<p>If an inversion-even function $p:G\to[0,1]$ specifies the off-diagonal bond probabilities by $q(\{x,y\})=p(yx^{-1})$, their row sum is $m=\sum_{z\ne e}p(z)$. For $m&lt;1$, the <a href="/tag/53Z9/">row-sum theorem</a> gives $\chi_q(x)\leq(1-m)^{-1}$ at every vertex and simultaneous almost-sure finiteness of all clusters. No support-generation hypothesis is needed for this estimate.</p><p>For an intensity kernel with $M&lt;\infty$, the <a href="/tag/A65C/">exponential family</a> instead has off-diagonal probabilities $1-e^{-\beta k(yx^{-1})}$. The inequality $1-e^{-t}\leq t$ bounds their row by $\beta M$, so the <a href="/tag/E771/">intensity bound</a> gives</p><div class="math-display">$$\beta M&lt;1\quad\Longrightarrow\quad\chi_\beta(x)\leq\frac1{1-\beta M}.$$</div><p>For $M&gt;0$, the <a href="/tag/JZ47/">threshold consequence</a> gives root and global critical intensities at least $M^{-1}$. If $M=0$, all off-diagonal intensities vanish, susceptibility is one and both kinds of threshold are infinite. This does not assert a transition at a finite intensity when $M&gt;0$.</p><p>The simple open graph is right-translation invariant in law, by <a href="/tag/6VY0/">product-law transport</a>, and its vertex observables therefore have the same distribution at every root. Arbitrary diagonal probabilities do not alter that graph law. Invariance of the entire configuration, including loop coordinates, would additionally require those diagonal marginals to be preserved by the action.</p>

## Concrete kernels {#section-examples}

<p>On $\mathbb Z^d$, the nearest-neighbour intensity $k(z)=C\mathbf1_{\{\|z\|_1=1\}}$ has $M=2dC$. For $d\geq1$ and $C&gt;0$, the preceding estimate reads $\chi_\beta\leq(1-2dC\beta)^{-1}$ when $2dC\beta&lt;1$, and the intensity thresholds are at least $(2dC)^{-1}$. For $d=0$ the vertex group is a singleton and the off-diagonal row is zero.</p><p>More generally, on any group choose $a\in G$ and take the intensity kernel</p><div class="math-display">$$k(z)=\mathbf1_{\{z=a\}}+\mathbf1_{\{z=a^{-1}\}}.$$</div><p>It is inversion-even and its total mass is two. If $a\ne e$, the off-diagonal mass is also two, yielding $\chi_{1/4}\leq2$ and threshold lower bounds $1/2$. If $a=a^{-1}\ne e$, the single nonzero kernel value is two: the two terms are added, not collapsed into one. This is an intensity kernel, so a value above one is allowed. If $a=e$, both contributions lie on the diagonal and the off-diagonal mass is zero.</p><p>The support may generate only a proper subgroup, leaving the possible-edge graph disconnected. None of the row estimates requires connectedness, and none turns this elementary small-intensity control into a claim of criticality or uniqueness.</p>

## Euclidean power-kernel tails {#section-power-tail}

<a id="tag-B2ZL" data-assertion="proposition" data-title="Omitted-row bounds for a Euclidean power-law intensity"></a>
<p>On $\mathbb Z^d$, $d\geq1$, use the norm $\|z\|_\infty=\max_i|z_i|$. Suppose $\alpha&gt;0$ and, for every $z\neq0$,</p>
<div class="math-display">$$c\|z\|_\infty^{-d-\alpha}\leq k(z)\leq C\|z\|_\infty^{-d-\alpha},\qquad 0&lt;c\leq C&lt;\infty.$$</div>
<p>For every real $R\geq1$,</p>
<div class="math-display">$$\frac{2dc}{\alpha\,2^\alpha}R^{-\alpha}\leq\sum_{\|z\|_\infty&gt;R}k(z)\leq\frac{2d\,3^{d-1}C\,2^\alpha}{\alpha}R^{-\alpha}.$$</div>
<p>The upper bound needs only the upper hypothesis on $k$. In particular the off-diagonal intensity row is finite. For an inversion-even kernel, closing all bonds of length greater than $R$ omits a probability row at most $\beta$ times the displayed upper bound in the exponential intensity family.</p>
<p><em>Proof.</em> The shell of radius $n\geq1$ has $(2n+1)^d-(2n-1)^d$ vertices. Integrating the derivative $d t^{d-1}$ of $t^d$ between $2n-1$ and $2n+1$ gives</p>
<div class="math-display">$$2d\,n^{d-1}\leq(2n+1)^d-(2n-1)^d\leq2d\,3^{d-1}n^{d-1}.$$</div>
<p>Multiplication by the kernel bounds reduces the omitted row to constant multiples of $\sum_{n&gt;R}n^{-1-\alpha}$. With $m=\lfloor R\rfloor\geq1$, comparison with integrals gives</p>
<div class="math-display">$$\frac{(m+1)^{-\alpha}}\alpha\leq\sum_{n=m+1}^\infty n^{-1-\alpha}\leq\frac{m^{-\alpha}}\alpha.$$</div>
<p>Since $m\geq R/2$ and $m+1\leq2R$, this proves the constants above. Summing the finitely many inner shells as well proves full row finiteness. Reindexing by displacement makes the same bound valid at every vertex, and $1-e^{-\beta k}\leq\beta k$ gives the probability-row estimate.</p>
<p>This supplies the omitted-kernel power bound used in the notes' cutoff-to-full ghost comparison, lines 5247–5273, for a kernel with the displayed pointwise upper estimate. Finite-range truncation on $\mathbb Z^d$ still leaves an infinite vertex set: the row-tail estimate alone does not show that its clusters have finite volume or finite moments.</p>

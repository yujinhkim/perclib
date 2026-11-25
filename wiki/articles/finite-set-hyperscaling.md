---
{
  "id": "finite-set-hyperscaling",
  "title": "Finite-set hyperscaling bounds",
  "subtitle": "Comparing the largest intersection with the sum of squared intersections",
  "kind": "method",
  "category": "Critical phenomena",
  "summary": "A global cluster tail and a rooted damping estimate control the largest-cluster quantile and averaged connectivity in every finite observation set. Exponent inequalities require separate asymptotic assumptions.",
  "context": ["Clusters are full-graph clusters intersected with a finite nonempty observation set; paths may leave the set.", "The global volume-tail exponent satisfies $\\delta>1$.", "The rooted exponential damping estimate is an explicit input from universal tightness."],
  "related": ["universal-tightness", "critical-exponents", "susceptibility", "hierarchical-two-point"],
  "sourceIds": ["notes"],
  "aliases": ["hyperscaling", "averaged connectivity", "fractal dimension", "largest-cluster quantile", "upper critical dimension"],
  "prototypeUses": []
}
---

## The finite-set estimate {#section-finite-set}

<a id="tag-WRHL" data-assertion="theorem" data-title="Finite-set hyperscaling from global tails and rooted damping"></a>
<p>Consider random clusters on a countable vertex set. Suppose $\delta&gt;1$, $C&gt;0$, and</p>
<div class="math-display">$$\sup_x\mathbb P(|K_x|\geq n)\leq Cn^{-1/\delta}\qquad(n\geq1).$$</div>
<p>For a finite nonempty set $\Lambda$, put $Z=\max_{x\in\Lambda}|K_x\cap\Lambda|$ and $M=\min\{m\geq1:\mathbb P(Z\geq m)\leq e^{-1}\}$. Assume the rooted damping estimate</p>
<div class="math-display">$$\mathbb P(|K_x\cap\Lambda|\geq\lambda M)\leq e^{1-\lambda/9}\mathbb P(|K_x\cap\Lambda|\geq M)\qquad(x\in V,\ \lambda\geq1).$$</div>
<p>Set</p>
<div class="math-display">$$L=C\left(\frac{\delta}{\delta-1}+9e^{8/9}\right),\qquad C_1=(4eL)^{\delta/(\delta+1)},\qquad C_2=L(4eL)^{(\delta-1)/(\delta+1)}.$$</div>
<p>Then</p>
<div class="math-display">$$M\leq C_1|\Lambda|^{\delta/(\delta+1)},\qquad \frac1{|\Lambda|}\sum_{v\in\Lambda}\mathbb P(x\leftrightarrow v)\leq C_2|\Lambda|^{-2/(\delta+1)}\quad(x\in V).$$</div>
<p>No transitivity is needed once the two displayed probability bounds hold uniformly in the root. The clusters must be those of a common random partition, so that their intersections partition $\Lambda$.</p>
<p><em>Proof.</em> Write $X_x=|K_x\cap\Lambda|$ and $\alpha=1/\delta\in(0,1)$. For $n\leq M$, the global bound gives $\mathbb P(X_x\geq n)\leq Cn^{-\alpha}$. For $n&gt;M$, rooted damping gives $\mathbb P(X_x\geq n)\leq C M^{-\alpha}e^{1-n/(9M)}$. Hence the integer tail-sum identity yields</p>
<div class="math-display">$$\begin{aligned}
\mathbb E X_x&\leq C\sum_{n=1}^M n^{-\alpha}+CeM^{-\alpha}\sum_{n&gt;M}e^{-n/(9M)}\\
&\leq\frac{C}{1-\alpha}M^{1-\alpha}+CeM^{-\alpha}\int_M^\infty e^{-t/(9M)}\,dt
=L M^{1-\alpha}.
\end{aligned}$$</div>
<p>The first sum is bounded by $1+\int_1^M t^{-\alpha}\,dt\leq M^{1-\alpha}/(1-\alpha)$. In the second sum the integrand is decreasing, giving the stated integral comparison.</p>
<p>For every configuration, let $C_i$ be the distinct full clusters meeting $\Lambda$. Counting ordered pairs gives</p>
<div class="math-display">$$\sum_{u,v\in\Lambda}\mathbf1_{\{u\leftrightarrow v\}}=\sum_i|C_i\cap\Lambda|^2\geq Z^2.$$</div>
<p>The quantile definition alone gives $M\geq2$ and $\mathbb P(Z\geq M-1)&gt;e^{-1}$, so $\mathbb E Z^2\geq M^2/(4e)$. Taking expectations in the pair identity and applying the bound on $\mathbb E X_u$ gives</p>
<div class="math-display">$$\frac{M^2}{4e}\leq\sum_{u\in\Lambda}\mathbb E X_u\leq|\Lambda|L M^{1-\alpha}.$$</div>
<p>Divide by $M^{1-\alpha}$ to obtain $M^{1+\alpha}\leq4eL|\Lambda|$, proving the first estimate. For any root $x$, insert it into $\sum_{v\in\Lambda}\mathbb P(x\leftrightarrow v)=\mathbb E X_x\leq L M^{1-\alpha}$ and divide by $|\Lambda|$. This gives the second estimate with the displayed constant.</p>
<p>The rooted damping estimate is the <a href="/tag/21D4/">universal-tightness input</a>. Its splitting argument is proved <a href="#section-rooted-damping">below</a>, separately from this calculation. Conversely, no separate lower-tail theorem for $Z$ is needed here: the elementary quantile property supplies the required second-moment lower bound. The restriction $\delta&gt;1$ is used in summing the small-size tail; the borderline $\delta=1$ requires a different logarithmic estimate.</p>

## Passing to exponents {#section-exponents}

<a id="tag-7VCS" data-assertion="corollary" data-title="Hyperscaling exponent inequalities from finite-set bounds"></a>
<p>Suppose the preceding hypotheses hold for a family of finite sets $\Lambda_R$, $R\to\infty$, and for some $d&gt;0$ and finite real $d_f,s$,</p>
<div class="math-display">$$|\Lambda_R|=R^{d+o(1)},\qquad M(\Lambda_R)=R^{d_f+o(1)},\qquad \sum_{v\in\Lambda_R}\mathbb P(o\leftrightarrow v)=R^{s+o(1)}.$$</div>
<p>Then</p>
<div class="math-display">$$\frac{d_f}{d}\leq\frac{\delta}{\delta+1},\qquad s\leq d\frac{\delta-1}{\delta+1}.$$</div>
<p>If $s=2-\eta$ is the chosen averaged two-point exponent, the latter inequality is $2-\eta\leq d(\delta-1)/(\delta+1)$. In particular, $\delta=2$ and $s=2$ require $d\geq6$.</p>
<p><em>Proof.</em> Take logarithms of the two finite-set inequalities, divide by $\log R$, and let $R\to\infty$. Fixed multiplicative constants contribute zero in this limit. The first gives $d_f\leq d\delta/(\delta+1)$. Multiplying the averaged-connectivity estimate by $|\Lambda_R|$ before taking logarithms gives $s\leq d(\delta-1)/(\delta+1)$. Substitute the stated values for the final assertion.</p>
<p>These conclusions assume the three asymptotic laws; they do not prove that the exponents exist. A pointwise two-point exponent may imply the displayed averaged law under suitable spatial hypotheses, but that implication must be established separately. Likewise, $d_f$ here describes the quantile scale, not an almost-sure fractal dimension assigned to an individual cluster.</p>
<p>Under transitivity, a logarithmic cluster-tail exponent with finite $\delta&gt;1$ also suffices for these exponent inequalities if rooted damping is available. For every $\delta'&gt;\delta$, the logarithmic tail law gives $\mathbb P(|K_o|\geq n)\leq C_{\delta'}n^{-1/\delta'}$, with transitivity making this uniform in the root. Apply the inequalities with $\delta'$ and then let $\delta'\downarrow\delta$. This limiting argument concerns exponents only and does not turn a logarithmic tail law into a fixed two-sided power comparison.</p>

## Source scope {#section-source}

<p>This supplies the finite-set calculation and exponent passage in the notes, lines 3220–3298 (S021). The source's global tail and rooted damping remain distinct hypotheses. The proof uses the quantile definition in place of the lower-tail half of universal tightness, and keeps the averaged two-point asymptotic separate from any pointwise spatial claim.</p>

## Splitting a connected witness {#section-splitting}

<a id="tag-DMI0" data-assertion="proposition" data-title="Marked tree splitting with a prescribed root covered"></a>
<p>Let $T$ be a finite tree and $A$ a set of $N$ marked vertices. If $k\geq1$ is an integer and $N\geq3^k$, its edges admit a partition into $m\geq3^{k-1}+1$ nonempty connected pieces such that every piece has between $3^{-k}N$ and $3^{1-k}N$ marked endpoints, with the upper bound strict. Their endpoint sets cover every vertex of $T$. In particular, any prescribed root belongs to at least one piece.</p>
<p><em>Proof.</em> We first split a tree with $n\geq3$ marked vertices into two pieces, each having between $n/3$ and $\lceil2n/3\rceil$ marked endpoints. Choose a vertex $v$ for which every component of $T\setminus\{v\}$ contains at most $n/2$ marks. Such a vertex exists: moving toward a component containing more than half the marks strictly decreases the sum of distances to the marked vertices.</p>
<p>Put $w=\mathbf1_{\{v\in A\}}$. The components at $v$ have integer masses at most $\lfloor n/2\rfloor$, with sum $n-w$. We select some of them whose total mass $s$ lies in the integer interval</p>
<div class="math-display">$$
L=\max\{\lceil n/3\rceil-w,\lfloor n/3\rfloor\}
\ \leq s\leq
U=\min\{\lceil2n/3\rceil-w,\lfloor2n/3\rfloor\}.
$$</div>
<p>Indeed, $\lfloor n/2\rfloor\leq U$, $2L-2\leq U$, and $n-w\geq L$, as is checked by writing $n=3q+r$, $r\in\{0,1,2\}$. If one component has mass at least $L$, take it. Otherwise add components until the sum first reaches $L$; the sum is at most $2L-2$. Give the selected branches, including their edges to $v$, to the first piece and all other branches to the second. Both are nonempty and connected. Their marked endpoint counts are $s+w$ and $n-s$, which have the required bounds. The possible shared mark at $v$ is included in both counts.</p>
<p>Now put $t=3^{-k}N\geq1$. Starting with the whole tree, split any piece having at least $3t$ marked endpoints by this construction. Each child has at least $t$ marks. A split strictly decreases the number of marks in either child, since $\lceil2n/3\rceil&lt;n$ for integer $n\geq3$; alternatively, each split increases the number of nonempty parts of the finite edge set. Thus the procedure terminates. Every final piece has marked mass in $[t,3t)$, and their endpoint sets still cover the tree. Since they cover $A$, $3tm&gt;N$, giving $m&gt;3^{k-1}$. Endpoint sets may overlap; the edge sets do not.</p>

## Rooted damping from BK {#section-rooted-damping}

<a id="tag-12NL" data-assertion="theorem" data-title="Maximum and rooted intersection tails from finite witness splitting"></a>
<p>Consider independent bond percolation on a countable graph, with arbitrary edge probabilities, and a finite nonempty observation set $\Lambda$. Write $X_u=|K_u\cap\Lambda|$, $Z=\max_{x\in\Lambda}X_x$, and $M=\min\{n\geq1:\mathbb P(Z\geq n)\leq e^{-1}\}$. Then, for every real $\lambda\geq1$ and integer $k\geq1$,</p>
<div class="math-display">$$
\begin{aligned}
\mathbb P(Z\geq3^k\lambda)&\leq\mathbb P(Z\geq\lambda)^{3^{k-1}+1},\\
\mathbb P(X_u\geq3^k\lambda)&\leq\mathbb P(X_u\geq\lambda)\mathbb P(Z\geq\lambda)^{3^{k-1}}\qquad(u\in V).
\end{aligned}
$$</div>
<p>Consequently, for $r\geq1$ and $0&lt;\varepsilon\leq1$,</p>
<div class="math-display">$$
\mathbb P(Z\geq rM)\leq e^{-r/9},\qquad
\mathbb P(X_u\geq rM)\leq e^{1-r/9}\mathbb P(X_u\geq M),\qquad
\mathbb P(Z&lt;\varepsilon M)\leq27\varepsilon.
$$</div>
<p><em>Proof.</em> First take a finite graph. On $X_u\geq3^k\lambda$, choose a spanning tree of the open cluster of $u$, marking its vertices in $\Lambda$. The splitting lemma supplies at least $3^{k-1}+1$ disjoint open edge sets. Each connects at least $\lambda$ marked vertices and therefore witnesses $Z\geq\lambda$. At least one contains $u$ and witnesses $X_u\geq\lambda$. Keep that piece and any $3^{k-1}$ others. BK bounds their disjoint occurrence by the product in the second inequality. The first follows in the same way from any cluster attaining the maximum, without prescribing a root. No union bound over choices of pieces is needed: their existence is precisely disjoint occurrence.</p>
<p>For a countable graph, exhaust the edge set by finite sets and keep $\Lambda\cup\{u\}$ as vertices. Every connection used here has a finite path, so the threshold events increase to those in the full graph. Passing to the limit proves both inequalities without local finiteness or summability assumptions. Paths may leave $\Lambda$.</p>
<p>If $1\leq r\leq9$, monotonicity and the quantile definition give the maximum bound, while $e^{1-r/9}\geq1$ gives the rooted bound. If $r\geq9$, take $k=\lfloor\log_3 r\rfloor$ and $\lambda=M$. Then $3^k\leq r$ and $3^{k-1}&gt;r/9$; the two amplification inequalities and $\mathbb P(Z\geq M)\leq e^{-1}$ give the asserted bounds, in fact a slightly smaller rooted factor.</p>
<p>For the lower tail, the claim is immediate if $27\varepsilon\geq1$ or $\varepsilon M\leq1$. Otherwise put $k=\lfloor\log_3(1/\varepsilon)\rfloor-1$ and $\lambda=(M-1)/3^k$. Then $k\geq1$, $\lambda\geq\varepsilon M&gt;1$, and $3^{k-1}&gt;1/(27\varepsilon)$. Since $M\geq2$ and $\mathbb P(Z\geq M-1)&gt;e^{-1}$, amplification gives, with $p=\mathbb P(Z\geq\varepsilon M)$,</p>
<div class="math-display">$$
e^{-1}&lt;\mathbb P(Z\geq M-1)\leq\mathbb P(Z\geq\lambda)^{3^{k-1}+1}\leq p^{1/(27\varepsilon)}.
$$</div>
<p>Hence $1-p\leq1-e^{-27\varepsilon}\leq27\varepsilon$.</p>
<p>This proves the rooted damping hypothesis used in the <a href="#section-finite-set">finite-set estimate</a>. Applied with the whole finite block as the observation set and all exterior edges removed, it also supplies rooted damping in <a href="/tag/655W/">the hierarchical sibling recursion</a>. The argument uses the marked-tree and BK mechanism of the notes, lines 3134–3218; the corresponding published locators are <a href="https://arxiv.org/pdf/2008.11197v2#page=14">Theorems 2.2–2.3 and Lemma 2.4, pp. 14–18</a>. The centroid construction above gives a separate proof of the splitting step. These are prose proofs, not claims of Lean compilation or reviewed source correspondence.</p>

## Bounds from window tails alone {#section-window-tails}

<a id="tag-UVQ6" data-assertion="theorem" data-title="Finite-window hyperscaling with explicit tail-exponent constants"></a>
<p>In independent bond percolation on a countable graph, let $\Lambda$ be finite and nonempty. Suppose $A&gt;0$, $0\leq\theta&lt;1$, and</p>
<div class="math-display">$$\mathbb P(|K_u\cap\Lambda|\geq n)\leq An^{-\theta}\qquad(u\in V,\ n\geq1).$$</div>
<p>With $M$ the largest-intersection quantile, put $H_\theta=(1-\theta)^{-1}+9e^{8/9}$. Then</p>
<div class="math-display">$$
M\leq(4eH_\theta A|\Lambda|)^{1/(1+\theta)},\qquad
\sum_{v\in\Lambda}\mathbb P(u\leftrightarrow v)
\leq H_\theta(4eH_\theta)^{(1-\theta)/(1+\theta)}A^{2/(1+\theta)}|\Lambda|^{(1-\theta)/(1+\theta)}.
$$</div>
<p>In particular, for $0\leq\theta\leq1/2$ the second prefactor can be replaced by the universal constant $4e(2+9e^{8/9})^2$. The assumption concerns intersections with this one window, not full-cluster volumes; it includes roots outside $\Lambda$.</p>
<p><em>Proof.</em> Write $X_u=|K_u\cap\Lambda|$. The <a href="/tag/12NL/">rooted-tail bound</a> supplies exponential damping above $M$. Summing the assumed tail up to $M$ and the damped tail afterwards gives, also when $\theta=0$,</p>
<div class="math-display">$$
\mathbb E X_u\leq A\sum_{n=1}^M n^{-\theta}+AeM^{-\theta}\sum_{n&gt;M}e^{-n/(9M)}
\leq A H_\theta M^{1-\theta}.
$$</div>
<p>The first sum is at most $M^{1-\theta}/(1-\theta)$, and the second is bounded by its decreasing-integrand comparison on $[M,\infty)$. As in <a href="/tag/WRHL/">the pair-count argument</a>, the partition identity and quantile minimality give</p>
<div class="math-display">$$
\frac{M^2}{4e}\leq\mathbb E Z^2\leq\sum_{x\in\Lambda}\mathbb E X_x
\leq |\Lambda|A H_\theta M^{1-\theta}.
$$</div>
<p>This proves the quantile estimate. Substitute it into the bound on $\mathbb E X_u=\sum_{v\in\Lambda}\mathbb P(u\leftrightarrow v)$ to obtain the second estimate. For $\theta\leq1/2$, $H_\theta\leq H=2+9e^{8/9}$ and $0\leq(1-\theta)/(1+\theta)\leq1$, so its prefactor is at most $H(4eH)$.</p>
<p>A uniform full-cluster tail implies the displayed window-tail hypothesis by inclusion. On a transitive model, a tail bound at one root is uniform in the root. This gives the probability inequality quoted in <a href="https://arxiv.org/pdf/2103.17013v1#page=16">Theorem 2.14</a>, with a constant independent of $\theta\in[0,1/2]$. The integer threshold is $n\geq1$; the source's displayed use of $n$ with a quantifier on a different variable is not copied here.</p>

## Keeping the polynomial tail under damping {#section-polynomial-damping}

<a id="tag-MJEP" data-assertion="corollary" data-title="Polynomial window tails with exponential damping and fractional moments"></a>
<p>In independent bond percolation on a countable graph, fix a finite nonempty window $\Lambda$ and any root $u$. Let $X=|K_u\cap\Lambda|$ and let $M$ be the largest-intersection quantile of $\Lambda$. If $A&gt;0$, $0\leq\theta&lt;1$, and $\mathbb P(X\geq n)\leq An^{-\theta}$ for every integer $n\geq1$, then</p>
<div class="math-display">$$\mathbb P(X\geq n)\leq eA\left(\frac{18}{n}\right)^\theta e^{-n/(18M)}\qquad(n\geq1).$$</div>
<p>For every real $p&gt;\theta$, this implies</p>
<div class="math-display">$$\mathbb E X^p\leq eA\,18^p p\,\Gamma(p-\theta)M^{p-\theta}.$$</div>
<p>The polynomial-tail assumption is needed only at this root. The scale $M$ still concerns the maximum over the window, not a quantile of $X$.</p>
<p><em>Proof.</em> For $n\leq18M$, the multiplier $e18^\theta e^{-n/(18M)}$ is at least one, so the assumed polynomial bound suffices. For $n&gt;18M$, <a href="/tag/12NL/">rooted damping</a> gives</p>
<div class="math-display">$$\mathbb P(X\geq n)\leq eAM^{-\theta}e^{-n/(9M)}.$$</div>
<p>Set $x=n/(18M)&gt;1$. Since $x^\theta e^{-x}\leq1$, the last expression is at most $eAM^{-\theta}x^{-\theta}e^{-x}$, which is the desired bound.</p>
<p>For $t&gt;0$, integer-valuedness and the fact that $s^{-\theta}e^{-s/(18M)}$ decreases give</p>
<div class="math-display">$$\mathbb P(X&gt;t)=\mathbb P(X\geq\lfloor t\rfloor+1)\leq eA18^\theta t^{-\theta}e^{-t/(18M)}.$$</div>
<p>Integrate against $pt^{p-1}\,dt$ and substitute $s=t/(18M)$. The integral at zero converges because $p&gt;\theta$; the exponential handles infinity. This gives the displayed gamma factor. In particular, $p=1$ yields $\mathbb E X\leq18eA\Gamma(1-\theta)M^{1-\theta}$.</p>
<p>The tail estimate is the assertion of <a href="https://arxiv.org/pdf/2008.11197v2#page=18">Corollary 2.6</a>; the first-moment case is the estimate used in its proof of Theorem 2.5. The fractional-moment conclusion records the same integration for $p&gt;\theta$. It makes no claim of a matching lower bound or an asymptotic moment formula.</p>

## Closing a power-law amplitude bootstrap {#section-amplitude-bootstrap}

<a id="tag-C9N6" data-assertion="proposition" data-title="Uniform tail amplitude from a two-scale contraction"></a>
<p>Fix real numbers $d&gt;0$, $0&lt;\alpha&lt;d$, $C_0&gt;0$ and an integer $r_0\geq1$, and put</p>
<div class="math-display">$$\theta=\frac{d-\alpha}{2d+\alpha},\qquad D=C_0\bigl((r_0+1)^{\alpha/2}+1\bigr),\qquad B=\max\{1,D^{(1+\theta)/(2\theta)}\}.$$</div>
<p>Let $p:\mathbb N_{\geq1}\to[0,1]$ satisfy $p(1)=1$ and $\sum_{n\geq1}p(n)&lt;\infty$. Assume that whenever $A\geq1$ satisfies $p(n)\leq An^{-\theta}$ for all $n\geq1$, one has, for all integers $n\geq1$ and $r\geq r_0$,</p>
<div class="math-display">$$p(n)^2\leq C_0\left[A r^{\alpha/2}n^{-(1+2\theta)/2}+A^{2/(1+\theta)}r^{-2d\theta/(1+\theta)}\right].$$</div>
<p>Assume also that $p$ is nonincreasing. Then $p(n)\leq Bn^{-\theta}$ for all $n\geq1$. The bound depends only on $d,\alpha,C_0,r_0$, not on $\sum_n p(n)$.</p>
<p><em>Proof.</em> Since $0&lt;\theta&lt;1/2$, monotonicity gives $np(n)\leq\sum_kp(k)$ and hence</p>
<div class="math-display">$$1\leq M:=\sup_{n\geq1}n^\theta p(n)&lt;\infty.$$</div>
<p>The supremum need not be attained. Its definition nevertheless gives $p(n)\leq Mn^{-\theta}$ for every $n$, so the assumed estimate applies with $A=M$. Set $s=(1-2\theta)/\alpha$ and choose the integer $r=\lceil r_0n^s\rceil$. Then $n^s\leq r\leq(r_0+1)n^s$. The identity $d(1-2\theta)=\alpha(1+\theta)$ makes both powers of $n$ in the estimate equal to $-2\theta$. Since $M\geq1$ and $2/(1+\theta)&gt;1$, it follows that</p>
<div class="math-display">$$p(n)^2\leq D M^{2/(1+\theta)}n^{-2\theta}.$$</div>
<p>Take square roots and then the supremum over $n$. This yields $M\leq\sqrt D\,M^{1/(1+\theta)}$. Dividing by the positive power of $M$ gives $M\leq D^{(1+\theta)/(2\theta)}\leq B$, as claimed.</p>
<p>In particular, consider independent bond percolation on a countable graph with root $o$, indexed by $0&lt;\beta\leq b&lt;\infty$. Suppose each edge probability $q_e(\beta)$ is nondecreasing and satisfies $q_e(\beta)\uparrow q_e(b)$ as $\beta\uparrow b$. If $\mathbb E_\beta|K_o|&lt;\infty$ for every $\beta&lt;b$, and the displayed two-term implication holds for $p_\beta(n)=\mathbb P_\beta(|K_o|\geq n)$ with the same constants for all such $\beta$, then</p>
<div class="math-display">$$\mathbb P_b(|K_o|\geq n)\leq Bn^{-\theta}\qquad(n\geq1).$$</div>
<p>Indeed, tail summation gives the required summability below $b$. Couple the bonds by independent uniforms $U_e$, declaring $e$ open when $U_e&lt;q_e(\beta)$. An open edge at $b$ is open at some smaller parameter, and any finite collection of such edges is simultaneously open sufficiently near $b$. The event $|K_o|\geq n$ has a finite witness: paths from $o$ to $n$ distinct vertices. Thus, along any sequence $\beta_k\uparrow b$, these events increase to their event at $b$. Continuity from below carries the uniform tail bound to the endpoint. No continuity of the infinite-cluster event is asserted.</p>
<p>This isolates the amplitude contraction and endpoint passage in <a href="https://arxiv.org/pdf/2008.11197v2#page=29">Section 4 of the power-law paper</a>. The first term in the assumed squared-tail estimate is linear in $A$, while the second has power $2/(1+\theta)$; taking the square root only after bounding both terms preserves the contraction. The proposition does not derive that estimate from the graph, identify $b$ with the percolation threshold, or establish subcritical finite susceptibility. Those are separate inputs, so this conditional closure is not a proof of the paper's full critical-tail theorem.</p>

---
{
  "id": "branching-random-walk",
  "title": "Branching random walk and Green diagrams",
  "subtitle": "Occupation identities and diagrams for finite-range and power-law walks",
  "kind": "model",
  "category": "Models",
  "summary": "Critical branching random walk has random-walk Green function as its expected occupation density. Fourier inversion gives diagram thresholds for nearest-neighbour and power-law steps, including the logarithmic boundary at tail exponent two.",
  "context": ["Independent offspring variables have finite mean $m$; children move independently according to a Markov kernel.", "Occupation counts retain multiplicity: different particles and different generations can visit the same site.", "The first Fourier calculation is for lazy nearest-neighbour walk on $\\mathbb Z^d$, $d\\geq1$."],
  "related": ["branching-processes", "exploration", "triangle-condition", "susceptibility"],
  "sourceIds": ["notes"],
  "aliases": ["branching random walk", "Green function", "bubble diagram", "triangle diagram", "upper critical dimension", "occupation density"],
  "prototypeUses": []
}
---

## The branching walk {#section-model}

<a id="tag-CYYG" data-assertion="definition" data-title="Branching random walk and its occupation counts"></a><p>Let $S$ be a countable state space and $P$ a Markov transition kernel on $S$. Begin with one particle at $x$. Each particle has an independent copy of a nonnegative integer-valued offspring variable $\xi$, with $m=\mathbb E\xi&lt;\infty$. Conditional on the parent's location $z$, each child independently moves according to $P(z,\cdot)$; these moves are independent of all offspring variables. Write $N_n(y)$ for the number of generation-$n$ particles at $y$, and</p><div class="math-display">$$L_y=\sum_{n\geq0}N_n(y)\in\mathbb N\cup\{\infty\}$$</div><p>for its total occupation count. The total population in generation $n$ is the <a href="/tag/NCWZ/">Galton–Watson generation size</a>. Criticality here means $m=1$; it refers to the branching mechanism.</p>

<a id="tag-94E7" data-assertion="proposition" data-title="First moments of branching-random-walk occupation"></a><p>For every $n\geq0$ and $y\in S$,</p><div class="math-display">$$\mathbb E_x N_n(y)=m^nP^n(x,y),\qquad \mathbb E_x L_y=\sum_{n\geq0}m^nP^n(x,y).$$</div><p>Here $P^0(x,y)=\mathbf1_{\{x=y\}}$ and $m^0=1$, including when $m=0$. At criticality, the expected occupation is exactly the Markov-chain Green function</p><div class="math-display">$$G(x,y)=\sum_{n\geq0}P^n(x,y).$$</div><p><em>Proof.</em> Conditional on generation $n$ and its locations, each particle at $z$ contributes an expected $mP(z,y)$ children at $y$. Taking expectations gives</p><div class="math-display">$$\mathbb E_xN_{n+1}(y)=m\sum_z\mathbb E_xN_n(z)P(z,y).$$</div><p>Induction and the Markov-kernel composition rule prove the first formula. Tonelli gives the occupation formula. When $m=0$, there are no children almost surely, so only generation zero contributes.</p><p>This is an expectation, not a hitting probability. The event that the branching walk ever visits $y$ has probability $\mathbb P_x(L_y&gt;0)\leq\min\{1,\mathbb E_xL_y\}$, and equality need not hold. A particle system can visit a site many times. Even at a nondegenerate critical offspring law, where the family tree is finite almost surely, expected occupation may be infinite on a recurrent underlying walk.</p>

## Independent collision counts {#section-collisions}

<a id="tag-4F49" data-assertion="proposition" data-title="Expected collision multiplicity of independent critical branching walks"></a><p>Let $L$ and $\widetilde L$ be the occupation fields of two independent critical branching random walks started at $x$ and $z$, using the same kernel $P$. If $G(x,y)$ and $G(z,y)$ are finite for each $y$, then the total number of pairs of visits to a common site, counted with multiplicity, satisfies</p><div class="math-display">$$\mathbb E\sum_yL_y\widetilde L_y=\sum_yG(x,y)G(z,y).$$</div><p>Either side may be infinite. In particular, for a symmetric translation-invariant kernel on $\mathbb Z^d$ and two walks started at zero, the right side is the bubble diagram $\sum_yG(0,y)^2$.</p><p><em>Proof.</em> Independence gives $\mathbb E[L_y\widetilde L_y]=\mathbb E L_y\,\mathbb E\widetilde L_y$; this follows first for bounded truncations and then by monotone convergence. Sum over $y$ using Tonelli and apply the occupation identity.</p><p>This counts pairs of particles or generations visiting a site, not the cardinality of the intersection of their ranges. A divergent expected count does not by itself imply an infinite count almost surely, or determine the probability that the ranges intersect. Such distinctions matter when using a diagram as a geometric heuristic.</p>

## Two visits in the same family tree {#section-pair-occupation}

<a id="tag-J1E9" data-assertion="proposition" data-title="Second occupation moment of a critical branching random walk"></a>
<p>Suppose the offspring mean is one and its variance is $\sigma^2&lt;\infty$, allowing $\sigma^2=0$. Assume $G(u,v)&lt;\infty$ for every pair of states, and write</p>
<div class="math-display">$$H(u,v)=\sum_{n\geq1}P^n(u,v)=\sum_wP(u,w)G(w,v).$$</div>
<p>For a single branching random walk started at $x$,</p>
<div class="math-display">$$\begin{aligned}
\mathbb E_x[L_yL_z]={}&\mathbf1_{\{y=z\}}G(x,y)+G(x,y)H(y,z)+G(x,z)H(z,y)\\
&+\sigma^2\sum_wG(x,w)H(w,y)H(w,z).
\end{aligned}$$</div>
<p>The equality is an equality of nonnegative extended quantities. In particular, finiteness of all first occupation moments does not require the sum on the second line to be finite. When $\sigma^2=0$, that line is defined to be zero.</p>
<p><em>Proof.</em> Expand $L_yL_z$ as the number of ordered pairs of particles whose locations are $y$ and $z$. Classify a pair by its genealogy. If both entries are the same particle, their expected number is $\mathbf1_{\{y=z\}}G(x,y)$.</p>
<p>If the first particle is a strict ancestor of the second, a particle at $y$ has an expected $H(y,z)$ strict descendants at $z$, by the first-moment identity summed over positive generations. Its future reproduction and displacements have the original laws, independently of the information that placed it at $y$. Summing over particles at $y$ gives $G(x,y)H(y,z)$. Reversing the ancestral relation gives $G(x,z)H(z,y)$.</p>
<p>Otherwise the pair has a unique most recent common ancestor, and the two particles lie in the subtrees of distinct children of that ancestor. Conditional on an ancestor at $w$ having $k$ children, there are $k(k-1)$ ordered choices of these children. For each chosen child, the expected total occupation at $y$, including that child itself after its first step, is $\sum_vP(w,v)G(v,y)=H(w,y)$. The two child subtrees and their first steps are independent. Averaging over $k$ therefore gives $\mathbb E[\xi(\xi-1)]H(w,y)H(w,z)=\sigma^2H(w,y)H(w,z)$ per ancestor at $w$. Summing over ancestors gives the second line.</p>
<p>All these decompositions count nonnegative terms, so Tonelli justifies the sums even when the second moment is infinite. They apply also to the deterministic one-child law: the family is then a single infinite walk, there are no distinct child subtrees, and only the first three terms remain.</p>
<p>The two factors of $H$ in the branching term start with separate child steps. Replacing them by $G$ would count visits at the common ancestor again, although those belong to the first three terms. Likewise, the product of first moments for two independent branching walks cannot replace this same-tree identity. Neither identity identifies a visit count with a hitting probability or with the percolation two-point function.</p>

## A precise Fourier calculation {#section-diagrams}

<p>Now let $P$ be lazy nearest-neighbour walk on $\mathbb Z^d$: a step stays put with probability $1/2$ and takes each of the $2d$ coordinate steps with probability $1/(4d)$. Write $G(u)=G(0,u)$ and define nonnegative extended sums</p><div class="math-display">$$B=\sum_uG(u)^2,\qquad T=\sum_{u,v}G(u)G(v-u)G(v).$$</div>

<a id="tag-E9BP" data-assertion="theorem" data-title="Green, bubble and triangle thresholds for lazy nearest-neighbour walk"></a><p>For this walk,</p><div class="math-display">$$G(0)&lt;\infty\ \Longleftrightarrow\ d&gt;2,\qquad B&lt;\infty\ \Longleftrightarrow\ d&gt;4,\qquad T&lt;\infty\ \Longleftrightarrow\ d&gt;6.$$</div><p><em>Proof.</em> Introduce $G_r(u)=\sum_{n\geq0}r^nP^n(0,u)$ for $0\leq r&lt;1$. It lies in $\ell^1(\mathbb Z^d)$, with total mass $(1-r)^{-1}$. The one-step Fourier transform on $[-\pi,\pi]^d$ is</p><div class="math-display">$$\varphi(k)=\frac12+\frac1{2d}\sum_{j=1}^d\cos k_j,\qquad \widehat G_r(k)=\frac1{1-r\varphi(k)}.$$</div><p>Absolute summability justifies multiplying transforms and inverting convolutions. Symmetry therefore gives, for $j=1,2,3$,</p><div class="math-display">$$(G_r^{*j})(0)=\frac1{(2\pi)^d}\int_{[-\pi,\pi]^d}\frac{dk}{(1-r\varphi(k))^j}.$$</div><p>The cases $j=1,2,3$ on the left are respectively $G_r(0)$, $\sum_uG_r(u)^2$ and $\sum_{u,v}G_r(u)G_r(v-u)G_r(v)$. As $r\uparrow1$, all their summands increase to the corresponding undamped values. Also $0\leq\varphi\leq1$, so the integrands increase. Monotone convergence on both sides yields the same identity with $r=1$, allowing infinite values.</p><p>The only point of the torus where $\varphi=1$ is zero. Moreover,</p><div class="math-display">$$1-\varphi(k)=\frac1{2d}\sum_{j=1}^d(1-\cos k_j)\asymp |k|^2\quad\text{near zero}.$$</div><p>Away from zero the denominator is bounded below. Thus the integral for convolution order $j$ is finite exactly when $\int_0^\varepsilon \rho^{d-1-2j}\,d\rho$ is finite, which is equivalent to $d&gt;2j$. This proves all three thresholds. At $d=2j$, the spatial-frequency integral with a small ball of radius $a$ removed diverges on the order of $\log(1/a)$ as $a\downarrow0$.</p>

## Long-range step distributions {#section-long-range-symbol}

<a id="tag-VJCW" data-assertion="theorem" data-title="Fourier symbol of a power-law lattice step distribution"></a>
<p>Let $p$ be a symmetric probability mass function on $\mathbb Z^d$, $d\geq1$, with $p(0)\geq1/2$. Suppose that for some $\alpha&gt;0$ and constants $0&lt;c\leq C&lt;\infty$,</p>
<div class="math-display">$$c|x|^{-d-\alpha}\leq p(x)\leq C|x|^{-d-\alpha}\qquad(x\ne0),$$</div>
<p>where $|\cdot|$ is the Euclidean norm. Write $\varphi(k)=\sum_xp(x)\cos(k\cdot x)$ for $k\in[-\pi,\pi]^d$. Then $0\leq\varphi\leq1$, and $\varphi(k)=1$ only at the origin of the torus. Uniformly as $|k|\downarrow0$,</p>
<div class="math-display">$$1-\varphi(k)\asymp
\begin{cases}
|k|^\alpha,&0&lt;\alpha&lt;2,\\
|k|^2\log(1/|k|),&\alpha=2,\\
|k|^2,&\alpha&gt;2.
\end{cases}$$</div>
<p><em>Proof.</em> Laziness gives $\varphi(k)\geq p(0)-(1-p(0))\geq0$. Every coordinate unit vector has positive mass, so $\sum_xp(x)(1-\cos(k\cdot x))$ vanishes only when every coordinate of $k$ is zero modulo $2\pi$. Continuity then bounds $1-\varphi$ away from zero outside any neighbourhood of that point.</p>
<p>Put $\rho=|k|$ and take $R=\rho^{-1}\geq2$. The inequalities $1-\cos u\leq\min\{u^2/2,2\}$ give</p>
<div class="math-display">$$1-\varphi(k)\leq C'\left[\rho^2\sum_{0&lt;|x|\leq R}|x|^{2-d-\alpha}
+\sum_{|x|&gt;R}|x|^{-d-\alpha}\right].$$</div>
<p>For the lower bound, retain only $|x|\leq R$, where $|k\cdot x|\leq1$ and $1-\cos(k\cdot x)\geq c'(k\cdot x)^2$. Sign changes cancel the mixed coordinate sums in the radial reference weight, and coordinate permutations make the diagonal sums equal. Hence</p>
<div class="math-display">$$1-\varphi(k)\geq c''\sum_{0&lt;|x|\leq R}|x|^{-d-\alpha}(k\cdot x)^2
=\frac{c''\rho^2}{d}\sum_{0&lt;|x|\leq R}|x|^{2-d-\alpha}.$$</div>
<p>Lattice shells give $\sum_{|x|&gt;R}|x|^{-d-\alpha}\asymp R^{-\alpha}$. The truncated sum is comparable to $R^{2-\alpha}$ for $\alpha&lt;2$, to $\log R$ for $\alpha=2$, and to $1$ for $\alpha&gt;2$: a dyadic annulus of radius $s$ contains order $s^d$ lattice points and contributes order $s^{2-\alpha}$. Inserting these estimates proves all three cases. Radial symmetry of $p$ itself is unnecessary; only its two-sided comparison with the radial weight was used.</p>

## Green-function diagram thresholds {#section-long-range-diagrams}

<a id="tag-1POM" data-assertion="theorem" data-title="Long-range Green, bubble and triangle finiteness including the logarithmic boundary"></a>
<p>For the walk with step distribution $p$ in <a href="/tag/VJCW/">VJCW</a>, put $G_r(x)=\sum_{n\geq0}r^np^{*n}(x)$, $0\leq r&lt;1$, and $G(x)=\sum_{n\geq0}p^{*n}(x)$. For each integer $j\geq1$, the extended convolution sum $D_j=(G^{*j})(0)$ satisfies</p>
<div class="math-display">$$D_j=\frac1{(2\pi)^d}\int_{[-\pi,\pi]^d}(1-\varphi(k))^{-j}\,dk.$$</div>
<p>Its finiteness criterion is</p>
<div class="math-display">$$D_j&lt;\infty\quad\Longleftrightarrow\quad
\begin{cases}
d&gt;j\alpha,&0&lt;\alpha&lt;2,\\
d&gt;2j\ \text{or}\ (d=2j\ \text{and}\ j&gt;1),&\alpha=2,\\
d&gt;2j,&\alpha&gt;2.
\end{cases}$$</div>
<p>Here $D_1=G(0)$, $D_2=\sum_xG(x)^2$ is the bubble, and $D_3=\sum_{x,y}G(x)G(y-x)G(y)$ is the triangle. In particular, at $\alpha=2$ the bubble is finite in dimension four and the triangle is finite in dimension six.</p>
<p><em>Proof.</em> For $r&lt;1$, $G_r\in\ell^1$ with sum $(1-r)^{-1}$ and Fourier transform $(1-r\varphi)^{-1}$. Multiplication of transforms and Fourier inversion give</p>
<div class="math-display">$$(G_r^{*j})(0)=\frac1{(2\pi)^d}\int_{[-\pi,\pi]^d}(1-r\varphi(k))^{-j}\,dk.$$</div>
<p>Every summand on the left increases as $r\uparrow1$. The integrands also increase because $\varphi\geq0$. Monotone convergence proves the extended identity without first assuming that $G$ or its diagrams are finite. Symmetry identifies the bubble and triangle sums.</p>
<p>Only a neighbourhood of zero can contribute a divergence. For $\alpha\ne2$, <a href="/tag/VJCW/">the symbol estimate</a> reduces integrability to that of $\int_0^\delta \rho^{d-1-jb}\,d\rho$, where $b=\min\{\alpha,2\}$. For $\alpha=2$ the corresponding integral is</p>
<div class="math-display">$$\int_0^\delta\rho^{d-1-2j}\bigl(\log(1/\rho)\bigr)^{-j}\,d\rho.$$</div>
<p>It converges for $d&gt;2j$ and diverges for $d&lt;2j$. At equality the substitution $u=\log(1/\rho)$ gives $\int_{\log(1/\delta)}^\infty u^{-j}\,du$, which is finite exactly when $j&gt;1$. This proves the criterion.</p>

## Discounted divergence orders {#section-discounted-diagrams}

<a id="tag-KEPD" data-assertion="proposition" data-title="Divergence orders of discounted long-range Green diagrams"></a>
<p>Under the same assumptions, let $D_j(r)=(G_r^{*j})(0)$ and $\varepsilon=1-r\downarrow0$. For $\alpha\ne2$ and $b=\min\{\alpha,2\}$,</p>
<div class="math-display">$$D_j(1-\varepsilon)\asymp
\begin{cases}
\varepsilon^{d/b-j},&d&lt;jb,\\
\log(1/\varepsilon),&d=jb,\\
1,&d&gt;jb.
\end{cases}$$</div>
<p>For $\alpha=2$, the orders are instead</p>
<div class="math-display">$$D_j(1-\varepsilon)\asymp
\begin{cases}
\varepsilon^{d/2-j}\bigl(\log(1/\varepsilon)\bigr)^{-d/2},&d&lt;2j,\\
\log\log(1/\varepsilon),&d=2,\ j=1,\\
1,&d&gt;2j\ \text{or}\ (d=2j,\ j&gt;1).
\end{cases}$$</div>
<p>The constants may depend on the fixed step law, $d$ and $j$, but not on $\varepsilon$. In each finite case, $D_j(r)\uparrow D_j&lt;\infty$.</p>
<p><em>Proof.</em> For $r\geq1/2$, $1-r\varphi=\varepsilon+r(1-\varphi)$ is comparable to $\varepsilon+(1-\varphi)$. The integral away from zero remains bounded, and $D_j(r)\geq1$ because every convolution factor has its generation-zero mass at the origin. For $\alpha\ne2$, split the radial integral at $\rho=\varepsilon^{1/b}$. The inner part has order $\varepsilon^{-j}\varepsilon^{d/b}$, and the outer part is comparable to $\int_{\varepsilon^{1/b}}^\delta \rho^{d-1-jb}\,d\rho$. The three cases follow.</p>
<p>For $\alpha=2$, take a fixed $\delta&lt;e^{-1}$ and define $\rho_\varepsilon\in(0,\delta)$ by $\rho_\varepsilon^2\log(1/\rho_\varepsilon)=\varepsilon$. This solution is unique for small $\varepsilon$, and</p>
<div class="math-display">$$\rho_\varepsilon\asymp\sqrt{\frac{\varepsilon}{\log(1/\varepsilon)}}.$$</div>
<p>The inner part has order $\varepsilon^{-j}\rho_\varepsilon^d$. When $d&lt;2j$, the outer integral has order $\rho_\varepsilon^{d-2j}(\log(1/\rho_\varepsilon))^{-j}$, the same quantity. This last integral comparison follows, for example, by differentiating $\rho^{d-2j}(\log(1/\rho))^{-j}$ near zero. At $d=2j$ it is $\int_{\rho_\varepsilon}^\delta d\rho/[\rho(\log(1/\rho))^j]$, giving $\log\log(1/\varepsilon)$ for $j=1$ and a bounded limit for $j&gt;1$. The finite cases also follow from <a href="/tag/1POM/">the undamped criterion</a> and monotone convergence.</p>

## What transfers to percolation {#section-diagram-transfer}

<a id="tag-T79N" data-assertion="proposition" data-title="Pointwise Green domination transfers finite diagram bounds"></a>
<p>Let a translation-invariant independent bond model on $\mathbb Z^d$ have two-point function $t(x)=\mathbb P(0\leftrightarrow x)$. Suppose the Green function above is finite and, for some $A&lt;\infty$,</p>
<div class="math-display">$$t(x)\leq A G(x)\qquad(x\in\mathbb Z^d),$$</div>
<p>including $x=0$. Then, for every integer $j\geq1$,</p>
<div class="math-display">$$(t^{*j})(0)\leq A^jD_j.$$</div>
<p>Thus every finite walk diagram listed in <a href="/tag/1POM/">1POM</a> gives a finite percolation diagram under this domination hypothesis. If also $t(x)\geq aG(x)$ for every $x$, for some $a&gt;0$, the same diagrams are finite or infinite together.</p>
<p><em>Proof.</em> Compare each product of $j$ factors in the nonnegative convolution sum, then sum. Translation invariance and the symmetry of connectivity identify the cases $j=2,3$ with the percolation bubble and triangle. The lower comparison follows in the same way.</p>
<p>The domination estimate is a separate model-specific input. A divergent walk diagram gives no conclusion from an upper bound alone. Nor does finite $D_3$ prove this input or any percolation critical exponent.</p>
<p>The step-law assumption is also essential in the notes' Gaussian Green-function heuristic. For a symmetric lazy law with $p(x)\asymp|x|^{-4}$ on $\mathbb Z^3$ (so $\alpha=1$), <a href="/tag/1POM/">1POM</a> makes the bubble finite. Such a law exists by assigning half the mass to zero and distributing the rest proportionally to $|x|^{-4}$. It cannot satisfy $G(x)\asymp|x|^{-1}$: the lower bound would make $\sum_xG(x)^2$ diverge. The <a href="/errata/notes/#walk-step-assumptions">source erratum</a> records this missing hypothesis. The $\alpha=2$ logarithms above describe this specified walk family, not the logarithmic corrections of finite-range critical percolation.</p>

## What the diagram says about percolation {#section-interpretation}

<p>The <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L481">branching-random-walk discussion in the notes</a> motivates the percolation triangle diagram by replacing the two-point function with a random-walk Green function. The calculation above makes the resulting threshold six exact for the specified walk. It does not prove that the percolation two-point function has that form, or that a particular percolation model satisfies the triangle condition.</p><p>Likewise, the familiar spatial estimate $G(0,x)\asymp |x|^{2-d}$ needs assumptions on the walk and a separate Green-function estimate; an arbitrary step distribution need not have this decay. No such spatial estimate is needed for the Fourier proof above. Long-range steps can change the small-frequency power, and hence the dimensional thresholds.</p><p>The bubble calculation gives a threshold four for the expected collision multiplicity. It cannot be substituted for the triangle diagram governing the mean-field percolation argument. The notes' path-and-cloud dimension count and prediction of logarithmic percolation corrections at dimension six remain heuristic here. The logarithmic divergence proved above concerns the Green-function integral, not percolation observables.</p>

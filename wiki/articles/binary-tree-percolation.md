---
{
  "id": "binary-tree-percolation",
  "title": "Percolation on the rooted binary tree",
  "subtitle": "Exact cluster laws and critical asymptotics",
  "kind": "model",
  "category": "Models",
  "summary": "The root cluster is a Binomial(2,p) family tree. Its finite-size law is Catalan, giving exact critical volume and intrinsic-arm asymptotics.",
  "context": ["The infinite rooted tree in which every vertex has two distinguished children.", "Independent bond percolation with homogeneous parameter $p\\in[0,1]$.", "The root cluster $K$ includes the root."],
  "related": ["branching-processes", "connectivity", "susceptibility", "exploration"],
  "sourceIds": ["notes"],
  "aliases": ["binary tree", "Catalan", "critical tree", "intrinsic one arm", "mean field"],
  "prototypeUses": []
}
---

## The branching representation {#section-branching}

<a id="tag-CQYY" data-assertion="proposition" data-title="Binary-tree cluster law and its phase transition"></a><p>The generation sizes of the root cluster form a Galton–Watson process with offspring law $\operatorname{Bin}(2,p)$. Consequently the root critical probability is $1/2$, and</p><div class="math-display">$$\mathbb P_p(|K|=\infty)=\begin{cases}0,&amp;0\leq p\leq\tfrac12,\\1-\left(\frac{1-p}{p}\right)^2,&amp;\tfrac12&lt;p\leq1.\end{cases}$$</div><p>For $p&lt;1/2$, $\mathbb E_p|K|=(1-2p)^{-1}$; for $p\geq1/2$ this expectation is infinite.</p><p><em>Proof.</em> The two child edges of each vertex are independent, and different vertices have disjoint sets of child edges. Every reached vertex therefore has an independent $\operatorname{Bin}(2,p)$ number of reached children. Its mean is $2p$, so the extinction and expectation statements follow from <a href="#/branching-processes">branching-process theory</a>. The offspring generating function is $\phi(s)=(1-p+ps)^2$. For $p&gt;0$, its fixed points are $1$ and $((1-p)/p)^2$; the extinction probability is the smaller fixed point in $[0,1]$. At $p=0$ the cluster is the singleton root.</p><p>This is the rooted tree with two children at every vertex, not a tree where the root has three neighbours. Changing the root degree changes the root-cluster distribution and its constants.</p>

## The finite-cluster distribution {#section-catalan}

<a id="tag-9K6O" data-assertion="proposition" data-title="Catalan law for finite root clusters"></a><p>For every integer $n\geq1$,</p><div class="math-display">$$\mathbb P_p(|K|=n)=\frac1{n+1}\binom{2n}{n}p^{n-1}(1-p)^{n+1}.$$</div><p>At the endpoints the formula uses $0^0=1$.</p><p><em>Proof.</em> A fixed connected subtree containing the root and having $n$ vertices has $n-1$ internal edges. Its vertices have $2n$ child slots altogether, of which $n-1$ lead to vertices of the subtree; hence it has $n+1$ child edges leaving it. It is exactly the open root cluster when the internal edges are open and those boundary edges are closed, an event of probability $p^{n-1}(1-p)^{n+1}$.</p><p>Let $C_n$ count these subtrees and put $C(z)=\sum_{n\geq1}C_nz^n$. Decomposition at the two distinguished children, allowing either subtree to be empty, gives</p><div class="math-display">$$C(z)=z(1+C(z))^2,\qquad C(z)=\frac{1-2z-\sqrt{1-4z}}{2z}.$$</div><p>The branch with zero constant term is forced. Expanding the square root by the binomial series gives $C_n=(n+1)^{-1}\binom{2n}{n}$. The cluster events for different subtrees are disjoint, so summing their common probability proves the formula.</p>

<a id="tag-AAZS" data-assertion="corollary" data-title="Exact critical binary-tree volume asymptotics"></a><p>At $p=1/2$, as $n\to\infty$,</p><div class="math-display">$$\mathbb P_{1/2}(|K|=n)\sim\frac1{\sqrt\pi}n^{-3/2},\qquad\mathbb P_{1/2}(|K|\geq n)\sim\frac2{\sqrt\pi}n^{-1/2}.$$</div><p><em>Proof.</em> The exact mass is $C_n4^{-n}$, and Stirling's formula gives $C_n\sim4^n/(\sqrt\pi n^{3/2})$. Critical extinction excludes an atom at infinite size. Summing the asymptotic masses and using $\sum_{k\geq n}k^{-3/2}\sim2n^{-1/2}$ gives the tail equivalent.</p>

## Intrinsic distance and connection probabilities {#section-distance}

<a id="tag-NDIC" data-assertion="proposition" data-title="Binary-tree critical intrinsic arm and two-point formula"></a><p>Let $r_n$ be the probability at $p=1/2$ that the root cluster reaches generation $n$. Then $r_0=1$ and</p><div class="math-display">$$r_{n+1}=r_n-\frac14r_n^2,\qquad r_n\sim\frac4n.$$</div><p>For any two vertices $x,y$ and any $p\in[0,1]$, their connection probability is $p^{d(x,y)}$, where $d$ is distance in the underlying tree and $p^0=1$.</p><p><em>Proof.</em> Each of the two child edges is open and continues for $n$ more generations with probability $r_n/2$, independently of the other child. Thus $r_{n+1}=1-(1-r_n/2)^2$. The critical offspring variance is $1/2$, so the branching-process survival asymptotic gives $r_n\sim4/n$. Finally, the unique path from $x$ to $y$ has $d(x,y)$ edges, and connection occurs exactly when all of them are open.</p><p>For a reached vertex, its distance from the root inside the cluster equals its distance in the underlying tree, because the path is unique. These intrinsic statements are not Euclidean spatial decay estimates.</p><p>Source: <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L379">notes, Chapter 2, Critical percolation on the binary tree</a>. The near-critical cutoff below specifies a joint-limit regime for the source's asymptotic discussion.</p>

## The near-critical cutoff {#section-cutoff}

<a id="tag-V5OZ" data-assertion="proposition" data-title="Binary-tree finite-cluster cutoff with an explicit joint-limit regime"></a><p>For $0&lt;p&lt;1$ and large $n$,</p><div class="math-display">$$\mathbb P_p(|K|=n)\sim\frac{1-p}{p\sqrt\pi}\,n^{-3/2}[4p(1-p)]^n,$$</div><p>with relative error depending only on $n$, hence uniformly in $p\in(0,1)$. In particular, if $p_n=1/2+\varepsilon_n$, $\varepsilon_n\to0$, and $n\varepsilon_n^4\to0$, then</p><div class="math-display">$$\mathbb P_{p_n}(|K|=n)\sim\frac1{\sqrt\pi}n^{-3/2}\exp(-4n\varepsilon_n^2).$$</div><p><em>Proof.</em> The exact Catalan law can be written as</p><div class="math-display">$$\mathbb P_p(|K|=n)=C_n4^{-n}\frac{1-p}{p}[4p(1-p)]^n.$$</div><p>The first asymptotic follows from $C_n4^{-n}\sim n^{-3/2}/\sqrt\pi$, whose relative error is independent of $p$. For the second, use $4p_n(1-p_n)=1-4\varepsilon_n^2$ and</p><div class="math-display">$$n\log(1-4\varepsilon_n^2)=-4n\varepsilon_n^2+O(n\varepsilon_n^4).$$</div><p>The error tends to zero by hypothesis, and $(1-p_n)/p_n\to1$. The exponential factor becomes appreciably smaller when $n$ is of order $|p-1/2|^{-2}$, giving the finite-cluster cutoff scale. These are unconditional probabilities of finite cluster sizes; on the supercritical side the remaining mass is at infinite size.</p>

## Moments across the cutoff {#section-moments}

<a id="tag-GGVG" data-assertion="proposition" data-title="Near-critical finite-cluster moments on the rooted binary tree"></a>
<p>For $s\geq0$ and $0&lt;p&lt;1$, define the finite-cluster moment by the sum</p>
<div class="math-display">$$M_s(p)=\sum_{n\geq1}n^s\mathbb P_p(|K|=n).$$</div>
<p>Put $\lambda(p)=-\log[4p(1-p)]$. As $p\to1/2$ with $p\neq1/2$, from either side,</p>
<div class="math-display">$$M_s(p)\sim\frac{\Gamma(s-1/2)}{\sqrt\pi}\lambda(p)^{-(s-1/2)}\quad(s&gt;1/2),\qquad M_{1/2}(p)\sim\frac1{\sqrt\pi}\log\frac1{\lambda(p)}.$$</div>
<p>For $0\leq s&lt;1/2$, instead $M_s(p)\to M_s(1/2)&lt;\infty$. Since $\lambda(p)\sim4(p-1/2)^2$, for every fixed $s&gt;1/2$ we also have</p>
<div class="math-display">$$\frac{M_{s+1}(p)}{M_s(p)}\sim\frac{s-1/2}{4(p-1/2)^2}.$$</div>
<p><em>Proof.</em> Write $a_n=C_n4^{-n}$, so $a_n\sim n^{-3/2}/\sqrt\pi$. The exact Catalan law gives</p>
<div class="math-display">$$M_s(p)=\frac{1-p}{p}\sum_{n\geq1}n^sa_ne^{-\lambda(p)n}.$$</div>
<p>For $s&gt;1/2$, set $a=s-1/2&gt;0$. The elementary Laplace sum has asymptotic</p>
<div class="math-display">$$\lambda^a\sum_{n\geq1}n^{a-1}e^{-\lambda n}=\lambda\sum_{n\geq1}(\lambda n)^{a-1}e^{-\lambda n}\longrightarrow\int_0^\infty t^{a-1}e^{-t}\,dt=\Gamma(a).$$</div>
<p>To justify the improper Riemann sum, first restrict to $\delta\leq\lambda n\leq R$. The omitted portion near zero is bounded by a constant times $\delta^a$, using $\sum_{n\leq N}n^{a-1}\leq C_aN^a$. The portion above $R$ tends uniformly to zero as $R\to\infty$, by exponential decay. On the middle interval ordinary Riemann sums apply. For any $\varepsilon&gt;0$, the asymptotic for $a_n$ bounds all sufficiently large summands between $(1\pm\varepsilon)n^{s-3/2}/\sqrt\pi$; finitely many remaining terms are negligible compared with $\lambda^{-a}$. Let $\varepsilon\downarrow0$ and use $(1-p)/p\to1$.</p>
<p>At $s=1/2$, the same comparison uses the exact sum $\sum_{n\geq1}e^{-\lambda n}/n=-\log(1-e^{-\lambda})\sim\log(1/\lambda)$. For $s&lt;1/2$, the bound $a_n\leq Cn^{-3/2}$ makes $\sum n^sa_n$ summable, so dominated convergence gives the finite limit. Finally $4p(1-p)=1-4(p-1/2)^2$, and $\Gamma(s+1/2)=(s-1/2)\Gamma(s-1/2)$ gives the moment-ratio equivalent.</p>
<p>Below criticality these are ordinary moments of $|K|$. Above criticality, $M_s$ omits the atom at infinite size; for every $s&gt;0$ the unconditional moment is infinite. Conditioning on a finite cluster divides every $M_s$ by the extinction probability, which tends to one, and leaves ratios of consecutive moments unchanged. In particular, the subcritical ratio $M_2/M_1\sim[8(p-1/2)^2]^{-1}$ gives a precise moment interpretation of the gap exponent two in the <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L455">notes' cutoff discussion</a>. This is a tree-model computation, not a proof of a percolation exponent in Euclidean space.</p>

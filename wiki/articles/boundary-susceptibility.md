---
{
  "id": "boundary-susceptibility",
  "title": "Susceptibility beyond a finite boundary",
  "subtitle": "A last-exit bound with the necessary positive part",
  "kind": "method",
  "category": "Critical phenomena",
  "summary": "BK and Cauchy–Schwarz bound the susceptibility available beyond a finite set. In the nontransitive formulation, a positive part is essential before squaring the lower bound.",
  "context": ["Independent bonds on a countable nonempty vertex set, with probabilities $1-e^{-\\beta J(u,v)}$.", "The symmetric nonnegative off-diagonal weights satisfy $\\sup_u\\sum_{v\\ne u}J(u,v)\\leq1$ and $\\beta>0$.", "Full susceptibilities are uniformly finite; paths outside a set use only its complement."],
  "related": ["integrated-susceptibility", "connection-kernels", "disjoint-occurrence", "triangle-condition"],
  "sourceIds": ["notes", "hutchcroft-triangle-2021"],
  "aliases": ["boundary susceptibility", "positive-part correction", "last exit", "quantitative triangle inequality"],
  "prototypeUses": []
}
---

## The boundary estimate {#section-bound}

<p>Write $T(u,v)=\mathbb P_\beta(u\leftrightarrow v)$, $\chi(u)=\sum_vT(u,v)$, $\chi_{\min}=\inf_u\chi(u)$ and $\chi_{\max}=\sup_u\chi(u)&lt;\infty$. For a finite nonempty set $S$, let $\chi_{S^c}(z)=\sum_{w\notin S}\mathbb P_\beta(z\leftrightarrow w\text{ using only }S^c)$ and define</p>
<div class="math-display">$$\Phi_\beta(S)=\sum_{v\in S}\sum_{z\notin S}J(v,z)\chi_{S^c}(z),\qquad Q(S)=\sum_{u\in S}\left(\sum_{v\in S}T(u,v)\right)^2.$$</div>

<a id="tag-67GX" data-assertion="theorem" data-title="Boundary susceptibility lower bound with positive part"></a>
<p>Under the preceding assumptions, put $L(S)=\sum_{u\in S}\sum_{w\notin S}T(u,w)$ and $x_+=\max(x,0)$. Then</p>
<div class="math-display">$$\Phi_\beta(S)\geq\frac{L(S)^2}{\beta^2\chi_{\max}Q(S)}\geq\frac{\left(\chi_{\min}|S|-\sum_{u,v\in S}T(u,v)\right)_+^2}{\beta^2\chi_{\max}Q(S)}.$$</div>
<p>The denominators are positive because $T(u,u)=1$ and $S$ is nonempty. If susceptibility is constant across roots, the expression inside the positive part equals $L(S)\geq0$, so the positive part can be omitted.</p>
<p><em>Proof.</em> Define $f(v)=\sum_{z\notin S}J(v,z)\chi_{S^c}(z)$ for $v\in S$. A connection from $u\in S$ to $w\notin S$ has a finite simple path. At its last exit from $S$, the path splits into a connection from $u$ to a boundary vertex $v$, the crossing edge $\{v,z\}$, and a connection from $z$ to $w$ entirely outside $S$. These three witnesses are edge-disjoint. BK and $1-e^{-\beta J(v,z)}\leq\beta J(v,z)$ give</p>
<div class="math-display">$$L(S)\leq\beta\sum_{v\in S}\left(\sum_{u\in S}T(u,v)\right)f(v).$$</div>
<p>For countably many bonds, apply finite-coordinate BK to finite path-witness events and pass upwards to their union. All subsequent sums are nonnegative. Since $0\leq f(v)\leq\chi_{\max}$ by the weight-row bound and $\sum_vf(v)=\Phi_\beta(S)$, Cauchy–Schwarz yields</p>
<div class="math-display">$$L(S)^2\leq\beta^2Q(S)\sum_{v\in S}f(v)^2\leq\beta^2Q(S)\chi_{\max}\Phi_\beta(S).$$</div>
<p>Finally $L(S)=\sum_{u\in S}\chi(u)-\sum_{u,v\in S}T(u,v)$ is nonnegative and at least the expression involving $\chi_{\min}$. Taking its positive part before squaring proves the second inequality.</p>

## Why the positive part is necessary {#section-counterexample}

<a id="tag-JTBG" data-assertion="proposition" data-title="A connected three-vertex counterexample to the unsigned-square formulation"></a>
<p>The preceding bound is false in general if its positive part is removed. Take the path with vertices $0,1,2$, intensity $\beta=1$, weights $J(0,1)=99/100$ and $J(1,2)=1/100$, and $S=\{0,1\}$. The weight rows are at most one. Put $p=1-e^{-99/100}$ and $t=1-e^{-1/100}$. Then</p>
<div class="math-display">$$\chi_{\min}=1+t+pt,\qquad\chi_{\max}=1+p+t,\qquad Q(S)=2(1+p)^2,\qquad\Phi_1(S)=\frac1{100}.$$</div>
<p>But the bound with the unsigned square would give</p>
<div class="math-display">$$\Phi_1(S)\geq\frac{4[p-t(1+p)]^2}{2(1+p+t)(1+p)^2}&gt;\frac{841}{10050}&gt;\frac1{100},$$</div>
<p>a contradiction.</p>
<p><em>Proof.</em> On a path, the two-edge connection probability is $pt$. Thus the three susceptibilities are $1+p+pt$, $1+p+t$ and $1+t+pt$. Since $p&gt;t$, their minimum and maximum are as displayed. The only boundary edge has weight $1/100$, and its outside endpoint is isolated after deleting $S$, so $\Phi_1(S)=1/100$. The inside sum is $2+2p$, making the proposed numerator the square of $2[t(1+p)-p]$.</p>
<p>For the strict numerical bound, $p&gt;3/5$ and $0&lt;t&lt;1/100$. The first follows from $e^{99/100}&gt;1+99/100+(99/100)^2/2+(99/100)^3/6&gt;5/2$; the second follows from $1-e^{-x}&lt;x$. Hence $2[p-t(1+p)]&gt;29/25$, while $1+p+t&lt;201/100$ and $2(1+p)^2&lt;8$. These rational bounds give the displayed contradiction without numerical approximation.</p>
<p>The graph is finite and connected, and all its susceptibilities are finite. The defect is therefore not caused by an infinite-volume limit or a disconnected host.</p>

## The weighted cluster moments {#section-diagrams}

<a id="tag-T7VI" data-assertion="proposition" data-title="Three- and four-point tree bounds for the weighted cluster moments"></a>
<p>Suppose the bond law is invariant under a transitive action with the <a href="/tag/N0HM/">mass-transport property</a>, and has finite susceptibility $\chi$. Write $K=K_o$ and use the diagrams $\Delta,A,B$ from the <a href="/tag/IZAO/">unimodular comparison</a>. Then</p>
<div class="math-display">$$\mathbb E\sum_{x,y\in K}T(x,y)\leq\chi\Delta,\qquad \mathbb E\sum_{a,b,c\in K}T(a,b)T(a,c)\leq\chi(2A+B).$$</div>
<p><em>Proof.</em> The three-point tree bound gives</p>
<div class="math-display">$$\sum_{x,y}T(x,y)\mathbb P(o,x,y\text{ connected})\leq\sum_{w,x,y}T(o,w)T(w,x)T(w,y)T(x,y)=\chi\Delta.$$</div>
<p>The last equality uses the constant diagonal triangle at $w$. For the second estimate use the three four-point tree shapes, allowing coincident branch points and empty path segments as in the <a href="/tag/AFH6/">multipoint tree bound</a>. Let $x$ be the branch point adjacent to the root leaf and $y$ the other branch point. After summing the three marked terminals with weights $T(a,b)T(a,c)$, each shape contributes $\sum_xT(o,x)D(x)$. The remaining diagram $D(x)$ is invariant in its root, so this equals $\chi D(o)$.</p>
<p>When the terminal $a$ is adjacent to the root-side branch point, summing $b,c$ gives</p>
<div class="math-display">$$D_B(o)=\sum_{a,y}T(o,a)T(o,y)T^2(a,y)^2.$$</div>
<p>Apply mass transport to $F(x,a)=T(x,a)\sum_yT(x,y)T^2(a,y)^2$. The incoming sum at $o$ is $\sum_yT^2(o,y)^2\sum_aT(o,a)T(a,y)=B$, proving $D_B(o)=B$.</p>
<p>When $b$ is adjacent to the root-side branch point, first summing $b,c$ gives</p>
<div class="math-display">$$D_A(o)=\sum_{a,y}T(o,y)T(y,a)T^2(o,a)T^2(y,a).$$</div>
<p>Apply mass transport to $F(x,y)=T(x,y)\sum_aT(y,a)T^2(x,a)T^2(y,a)$. Its incoming sum is</p>
<div class="math-display">$$\sum_aT(o,a)T^2(o,a)\sum_yT(o,y)T^2(y,a)=A.$$</div>
<p>The third shape has $c$ adjacent to the root-side branch point and gives the same value by exchanging $b,c$. Thus the total is $\chi(B+2A)$. All reindexings involve nonnegative sums, and the diagram comparison makes the resulting bounds finite.</p>

## A quadratic triangle bound {#section-quadratic}

<a id="tag-4KBG" data-assertion="theorem" data-title="Quadratic susceptibility lower derivative bound from the triangle diagram"></a>
<p>Let the intensity weights be invariant under a transitive action with the mass-transport property and have common row sum $0&lt;R\leq1$. Suppose $0\leq a&lt;b&lt;\infty$ and $\chi(\beta)&lt;\infty$ for every $\beta\in(a,b)$. Let $\Delta(\beta)=T_\beta^3(o,o)$. Then $\chi$ is locally Lipschitz and, almost everywhere on $(a,b)$,</p>
<div class="math-display">$$\chi'(\beta)=\mathbb E_\beta\Phi_\beta(K_o)\geq\frac{(\chi(\beta)-\Delta(\beta))_+^2}{\beta^2(2A(\beta)+B(\beta))}\geq\frac{(\chi(\beta)-\Delta(\beta))_+^2}{3\beta^2\Delta(\beta)^2}.$$</div>
<p>If additionally $\chi(b)=\infty$ and $\Delta(\beta)\leq D&lt;\infty$ on $(a,b)$, then for all $\beta$ sufficiently close to $b$,</p>
<div class="math-display">$$\frac1{R(b-\beta)}\leq\chi(\beta)\leq\frac{12b^2D^2}{b-\beta}.$$</div>
<p><em>Proof.</em> The finite-volume Russo identity for the root susceptibility is the sum over oriented pairs $u\ne v$ and targets $x$ of</p>
<div class="math-display">$$J(u,v)\mathbb P_\beta(o\leftrightarrow u,\ v\leftrightarrow x,\ o\not\leftrightarrow v),$$</div>
<p>with connections restricted to the finite volume. The closed-edge factor is included by the distinct-cluster event. On a compact parameter interval with right endpoint $t&lt;b$, BK bounds each summand by $J(u,v)T_t(o,u)T_t(v,x)$. Summing this bound gives $R\chi(t)^2&lt;\infty$. Under finite-volume exhaustion every indicator in the displayed event converges: connections have finite witnesses and a nonconnection persists unless a full connection eventually appears. Dominated convergence therefore applies to the sum and to its parameter integral. It gives local Lipschitz regularity and the infinite-volume identity almost everywhere.</p>
<p>Finite susceptibility makes $K_o$ finite almost surely. Conditional on $K_o=S$, the bonds outside $S$ retain their product law, while every boundary bond is closed. Summing over targets outside $S$ therefore identifies the preceding derivative with $\mathbb E\Phi_\beta(S)$.</p>
<p>Fix a parameter where this identity holds and suppress $\beta$. Put $U=\sum_{x,y\in K}T(x,y)$, $V=\sum_{a,b,c\in K}T(a,b)T(a,c)$, and $X=\chi|K|-U$. For each finite cluster, $X\geq0$ and $V\geq1$. The boundary estimate and Cauchy–Schwarz give</p>
<div class="math-display">$$\chi'\geq\frac1{\beta^2\chi}\mathbb E\frac{X^2}{V}\geq\frac{(\mathbb E X)^2}{\beta^2\chi\,\mathbb E V}.$$</div>
<p>The weighted moment estimates imply $\mathbb E X\geq\chi(\chi-\Delta)_+$ and $\mathbb E V\leq\chi(2A+B)$. Substitute these and then use $B\leq A\leq\Delta^2$ to obtain the displayed differential bounds.</p>
<p>For the endpoint conclusion, finite-volume continuity gives $\chi(\beta)\to\infty$ as $\beta\uparrow b$, so eventually $\chi\geq2D$. The lower derivative bound then gives $\chi'\geq\chi^2/(12b^2D^2)$. Integrate $(1/\chi)'\leq-1/(12b^2D^2)$ up to $b$ to obtain the upper susceptibility bound. The <a href="/tag/MXGM/">universal upper derivative bound</a> gives the lower susceptibility bound. Identifying $b$ with a critical parameter still requires the stated finiteness and divergence hypotheses.</p>
<p>The square in this result is important. The displayed Cauchy–Schwarz calculation in the notes yields $(\chi-\Delta)_+^2/(\beta^2(2A+B))$ from its stated inputs; it does not yield the larger numerator $\chi(\chi-\Delta)$ when $\chi&gt;\Delta$. Thus this proves a weaker quantitative inequality and the bounded-triangle susceptibility consequence, not the stronger formula stated as S010. The next section shows that the stronger formula itself fails at small intensity.</p>

## The stronger numerator fails at small intensity {#section-small-intensity}

<a id="tag-MTYL" data-assertion="proposition" data-title="The normalized infinite line contradicts the stronger triangle formula"></a>
<p>On $\mathbb Z$, put weight $1/2$ on each nearest-neighbour edge and zero on every other off-diagonal pair. The weight row is one. At intensity $\beta&gt;0$, write $p=1-e^{-\beta/2}$. Then</p>
<div class="math-display">$$T_\beta(x,y)=p^{|x-y|},\qquad\chi(\beta)=\frac{1+p}{1-p}=2e^{\beta/2}-1,\qquad\chi'(\beta)=e^{\beta/2},$$</div>
<div class="math-display">$$\Delta(\beta)=1+\frac{6p^2}{(1-p^2)^2}.$$</div>
<p>This is an infinite connected transitive model with the mass-transport property and finite susceptibility at every finite intensity. Nevertheless, for all sufficiently small $\beta&gt;0$,</p>
<div class="math-display">$$\chi'(\beta)&lt;\frac{\chi(\beta)(\chi(\beta)-\Delta(\beta))}{3\beta^2\Delta(\beta)^2}.$$</div>
<p><em>Proof.</em> The path between two vertices is unique, giving the two-point function. Summing its geometric series gives $\chi$ and differentiating gives $\chi'$. For the triangle, $|x|+|x-y|+|y|$ is twice the range of $\{0,x,y\}$. There are $6n$ ordered pairs $(x,y)$ of range $n\geq1$: $2n+1$ with both entries nonnegative, $2n+1$ with both nonpositive, and $2(n-1)$ straddling zero. Thus</p>
<div class="math-display">$$\Delta=1+6\sum_{n\geq1}np^{2n}=1+\frac{6p^2}{(1-p^2)^2}.$$</div>
<p>As $\beta\downarrow0$, $p\sim\beta/2$, $\chi=1+\beta+O(\beta^2)$ and $\Delta=1+O(\beta^2)$. The proposed lower bound is therefore asymptotic to $1/(3\beta)$, while $\chi'\to1$. This proves the contradiction. The finite susceptibility also shows that all finite intensities lie below the infinite-cluster threshold; the example is not using a supercritical parameter.</p>
<p>At $\beta=0.01$, the derivative is approximately $1.00501$, whereas the proposed bound is approximately $33.23937$. The asymptotic proof does not depend on these numerical values.</p>

<a id="tag-1EWX" data-assertion="proposition" data-title="Small-intensity susceptibility and triangle bounds for normalized models"></a>
<p>More generally, for any countable transitive independent-bond intensity model with symmetric nonnegative weights of row sum one, and $0&lt;\beta&lt;1$,</p>
<div class="math-display">$$1+\beta-\frac{\beta^2}{2}\leq\chi(\beta)\leq\frac1{1-\beta},\qquad 1\leq\Delta(\beta)\leq1+3\left(\frac\beta{1-\beta}\right)^2+\left(\frac\beta{1-\beta}\right)^3.$$</div>
<p>The susceptibility is locally Lipschitz on $(0,1)$, with $\chi'\leq(1-\beta)^{-2}$ almost everywhere. Consequently the stronger source formula fails almost everywhere for all sufficiently small intensities. This obstruction does not rely on an infinite critical parameter.</p>
<p><em>Proof.</em> Direct edges give $\chi\geq1+\sum_{v\ne o}(1-e^{-\beta J(o,v)})$. Use $1-e^{-x}\geq x-x^2/2$, the normalized row, and $\sum_vJ(o,v)^2\leq1$ to obtain the lower bound. For the upper bound, a connection has a simple path witness. Its probability is the product of its edge probabilities, each at most $\beta J$. Summing over simple paths and then over all walks only increases this nonnegative sum. The total weight of length-$n$ walks is at most $\beta^n$, by induction using the row sum. Summing over $n\geq0$ gives $(1-\beta)^{-1}$.</p>
<p>Write $T=I+S$. The matrix $S$ is nonnegative with zero diagonal and constant row sum $s=\chi-1\leq\beta/(1-\beta)$. Nonnegative summation gives row sums $s^k$ for $S^k$, so</p>
<div class="math-display">$$\Delta=(I+S)^3(o,o)=1+3S^2(o,o)+S^3(o,o)\leq1+3s^2+s^3.$$</div>
<p>The derivative bound follows from the finite-susceptibility <a href="/tag/MXGM/">local regularity and upper derivative estimate</a>. The displayed inequalities imply $\chi=1+\beta+O(\beta^2)$ and $\Delta=1+O(\beta^2)$, so the stronger source right side grows as $1/(3\beta)$, whereas the derivative is bounded almost everywhere. In particular, this argument applies also to normalized transitive models with a finite critical point.</p>

## Source scope {#section-source}

<p>S011 of the pinned notes, lines 1712–1801, states the nontransitive bound with an unsigned square. Its proof bounds the possibly negative expression by a nonnegative Cauchy–Schwarz term, then squares; that last operation needs the positive-part correction above. The stronger formulation using the actual mass $L(S)$ avoids the problem. The transitive use in the subsequent quantitative triangle argument has $\chi_{\min}=\chi_{\max}$, so its numerator is already nonnegative. This correction does not by itself prove that subsequent probabilistic argument.</p>

<p>The corresponding displays also occur in the cited paper: Lemma 2.1 and equations (2.4)–(2.5), printed pages 11–12 of the versioned PDF. The source reading map records the checked locations. The independent small-intensity counterexamples above rule out the stronger formula as stated for all positive subcritical parameters; they do not address a differently normalized or restricted replacement.</p>

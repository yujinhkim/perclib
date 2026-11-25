---
{
  "id": "hierarchical-runaway",
  "title": "The hierarchical runaway observable",
  "subtitle": "Amplification across blocks and the finite-susceptibility contradiction",
  "kind": "method",
  "category": "Critical phenomena",
  "summary": "Independent block clusters and direct connecting edges give a quantitative quantile amplification. Finite susceptibility forbids the resulting exponential growth, and finite-block continuity extends the bound to an endpoint.",
  "context": ["The standard hierarchical lattice has level-n blocks of size $L^{dn}$, for integers $L\\geq2$ and $d\\geq1$.", "The intensity model is translation-invariant, and weights at hierarchical level j are at least $cL^{-(d+\\alpha)j}$ with $0<\\alpha<d$.", "Clusters in this article are restricted to their finite block, not full-cluster intersections with it."],
  "related": ["hierarchical-two-point", "finite-random-graphs", "exponential-moments", "multipoint-trees", "universal-tightness"],
  "sourceIds": ["notes", "hutchcroft-hierarchical-2021"],
  "aliases": ["runaway observable", "hierarchical amplification", "block quantile", "scaling catastrophe"],
  "prototypeUses": []
}
---

## Amplifying a large block quantile {#section-amplification}

<a id="tag-7AER" data-assertion="theorem" data-title="Quantitative hierarchical block-quantile amplification"></a>
<p>On the standard hierarchical lattice, fix integers $L\geq2$, $d\geq1$, and constants $c&gt;0$, $0&lt;\alpha&lt;d$. Use independent bonds of probabilities $1-e^{-\beta J(u,v)}$, with finite nonnegative translation-invariant weights satisfying</p>
<div class="math-display">$$J(u,v)\geq cL^{-(d+\alpha)j}\quad\text{when }u,v\text{ first share a level-}j\text{ block}.$$</div>
<p>Let $Z_n$ be the largest cluster size using only edges inside a level-$n$ block, and define $R_n(\beta)=\min\{m\geq1:\mathbb P_\beta(Z_n\geq m)\leq e^{-1}\}$. Translation invariance makes this independent of the chosen block. Choose an integer $\ell\geq1$ such that, with $N=L^{d\ell}$,</p>
<div class="math-display">$$e^{-N/(8e)}\leq\frac14,\qquad L^{(d-\alpha)\ell}\geq16e^2,$$</div>
<p>and set</p>
<div class="math-display">$$A=\frac4c L^{(d+\alpha)\ell}\log(2N^2).$$</div>
<p>For every $\beta&gt;0$ and integer $n\geq0$,</p>
<div class="math-display">$$R_n(\beta)^2\geq\frac A\beta L^{(d+\alpha)n}\quad\Longrightarrow\quad R_{n+\ell}(\beta)^2\geq\frac A\beta L^{(d+\alpha)(n+\ell)}.$$</div>
<p>Such $\ell$ exist because $\alpha&lt;d$. This statement needs no critical-parameter or susceptibility assumption.</p>
<p><em>Proof.</em> A level-$(n+\ell)$ block contains $N$ disjoint level-$n$ blocks. Write $R=R_n(\beta)$. Since $2\leq R\leq L^{dn}+1$ and $\mathbb P(Z_n\geq R-1)&gt;e^{-1}$, each small block has probability at least $e^{-1}$ of containing a cluster of size at least $R/2$. Call such a block good, and choose one of its largest clusters by a fixed tie-breaking rule. Goodness depends only on internal edges, so the good-block indicators are independent.</p>
<p>If $G$ is their number, an exponential Markov bound gives</p>
<div class="math-display">$$\mathbb P\left(G&lt;\frac N{2e}\right)\leq e^{-N/(8e)}\leq\frac14.$$</div>
<p>For completeness, with $t=\log2$ the product of the Bernoulli Laplace transforms is at most $\exp[-(N/e)(1-e^{-t})]$. Multiplying by $\exp[tN/(2e)]$ gives an exponent at most $-N/(8e)$, since $(1-\log2)/2&gt;1/8$.</p>
<p>Condition on all small-block interiors. Between selected clusters $C_i,C_j$ in distinct good blocks, every edge has weight at least $cL^{-(d+\alpha)(n+\ell)}$. The probability that no direct edge joins them is therefore at most</p>
<div class="math-display">$$\exp\!\left[-\beta cL^{-(d+\alpha)(n+\ell)}|C_i||C_j|\right]\leq\exp\!\left[-\frac{cA}4L^{-(d+\alpha)\ell}\right]=\frac1{2N^2}.$$</div>
<p>Here the last inequality uses the assumed lower bound on $R^2$ and $|C_i|,|C_j|\geq R/2$. The connecting edges have not been exposed. A union bound over fewer than $N^2/2$ cluster pairs shows that, conditionally, all pairs have a direct connection with probability at least $3/4$.</p>
<p>With probability at least $1/2&gt;e^{-1}$, there are at least $N/(2e)$ good clusters and they all belong to one larger cluster. Its size is at least $NR/(4e)$. The quantile definition gives $R_{n+\ell}\geq NR/(4e)$, also when this threshold is not an integer: apply the probability bound at its ceiling. Hence</p>
<div class="math-display">$$R_{n+\ell}^2\geq\frac{L^{2d\ell}}{16e^2}R_n^2\geq\frac A\beta L^{(d+\alpha)(n+\ell)}\frac{L^{(d-\alpha)\ell}}{16e^2}\geq\frac A\beta L^{(d+\alpha)(n+\ell)}.$$</div>
<p>The argument deliberately asks for every pair of selected clusters to be connected directly. This costs a large fixed $A$, but avoids a separate random-graph giant-component theorem.</p>

## Ruling out runaway growth {#section-bound}

<a id="tag-2XJX" data-assertion="theorem" data-title="Hierarchical block-quantile bound from finite susceptibility and endpoint continuity"></a>
<p>In the preceding model, with the same $\ell,A$, if $\beta&gt;0$ and the full-model susceptibility $\chi(\beta)$ is finite, then</p>
<div class="math-display">$$R_n(\beta)^2&lt;\frac A\beta L^{(d+\alpha)n}\qquad(n\geq0).$$</div>
<p>More generally, if $0\leq a&lt;b&lt;\infty$, $b&gt;0$, and $\chi(\beta)&lt;\infty$ for every $\beta\in(a,b)$, then</p>
<div class="math-display">$$R_n(\beta)^2\leq\frac A b L^{(d+\alpha)n}\qquad(n\geq0,\ 0\leq\beta\leq b).$$</div>
<p><em>Proof.</em> Fix a positive parameter with finite susceptibility $\chi$. Transitivity and the <a href="/tag/Y84V/">tree-graph moments</a> give the <a href="/tag/SNB3/">exponential full-cluster tail</a></p>
<div class="math-display">$$\mathbb P_\beta(|K_x|\geq k)\leq(1+\chi^{-1})e^{-k/(2\chi^2)}.$$</div>
<p>A union bound over the $L^{dn}$ vertices of a level-$n$ block therefore gives</p>
<div class="math-display">$$R_n(\beta)\leq\left\lceil2\chi^2\left(dn\log L+\log(1+\chi^{-1})+1\right)\right\rceil=O_\beta(n+1).$$</div>
<p>If the first asserted bound failed at any scale $n$, amplification would propagate its failure to every $n+k\ell$. It would force $R_{n+k\ell}\geq\sqrt{A/\beta}\,L^{(d+\alpha)(n+k\ell)/2}$, contradicting the linear bound as $k\to\infty$. This proves the strict inequality.</p>
<p>For the endpoint claim fix $n$ and write $m=R_n(b)$. The block has finitely many edges with finite weights, so each probability $\mathbb P_\beta(Z_n\geq k)$ is continuous in $\beta$. Since $\mathbb P_b(Z_n\geq m-1)&gt;e^{-1}$, the same strict inequality holds sufficiently close to $b$ from below. Monotonicity gives $R_n(\beta)\leq R_n(b)$, so in fact $R_n(\beta)=m$ for all sufficiently close lower parameters. Passing to the limit in the first bound yields $R_n(b)^2\leq(A/b)L^{(d+\alpha)n}$. Finally $R_n(\beta)\leq R_n(b)$ for $0\leq\beta\leq b$.</p>
<p>This is the runaway-observable mechanism in the notes, lines 4040–4139 (S026–S027). Applying it with $b=\beta_c$ still requires a finite positive critical parameter and finite susceptibility below it. Those sharpness inputs are not consequences of block amplification. The subsequent expected-size recursion and restricted-to-unrestricted two-point estimates are also separate steps.</p>

## Identifying a finite critical intensity {#section-critical-intensity}

<a id="tag-FF30" data-assertion="theorem" data-title="Hierarchical critical intensity and boundary flux from amplification and sharpness"></a>
<p>In the model of <a href="/tag/7AER/">the amplification theorem</a>, assume also that the weights are symmetric and have finite common off-diagonal row sum</p>
<div class="math-display">$$B=\sum_{v\ne o}J(o,v)&lt;\infty.$$</div>
<p>The lower bound on the weights gives $B&gt;0$. Let $\beta_c$ be the critical intensity, and retain the constant $A$ from that theorem. Then</p>
<div class="math-display">$$0&lt;\frac1B\leq\beta_c\leq\frac A4&lt;\infty,\qquad R_n(\beta_c)^2\leq\frac A{\beta_c}L^{(d+\alpha)n}\quad(n\geq0).$$</div>
<p>For every finite $T\ni o$, writing $\tau_{T,\beta_c}(o,u)$ for internal connectivity, one also has</p>
<div class="math-display">$$\beta_c\sum_{u\in T}\tau_{T,\beta_c}(o,u)\sum_{v\notin T}J(u,v)\geq1.$$</div>
<p><em>Proof.</em> The row-sum bound gives $\beta_c\geq1/B$. The <a href="/articles/integrated-susceptibility/#section-finite-set">finite-set sharpness argument</a> gives finite susceptibility at every finite $\beta&lt;\beta_c$, including when the extended threshold might initially be infinite. Hence <a href="/tag/2XJX/">the runaway bound</a> applies at every $0&lt;\beta&lt;\beta_c$. A level-zero block consists of one vertex, so $R_0(\beta)=2$. Taking $n=0$ in that bound gives $4&lt;A/\beta$, or $\beta&lt;A/4$. Thus every positive subcritical intensity is less than $A/4$, which rules out an infinite threshold and yields $\beta_c\leq A/4$. The endpoint part of 2XJX now applies with $b=\beta_c$ and gives the quantile estimate.</p>
<p>For the boundary assertion, put</p>
<div class="math-display">$$\Phi_\beta(T)=\sum_{u\in T}\tau_{T,\beta}(o,u)\sum_{v\notin T}(1-e^{-\beta J(u,v)}).$$</div>
<p>The <a href="https://github.com/tomhutchcroft/lrp/blob/fa3d1bd9b862d919a74c92493e14cbda5c967cf5/wiki/articles/finite-size-sharpness.md#L44">canonical finite-size characterization</a> and continuity of $\Phi_\beta(T)$ imply $\Phi_{\beta_c}(T)\geq1$: a strict contraction at $\beta_c$ would persist at a larger intensity and force finite susceptibility there. Continuity holds because the internal graph is finite and the exterior probability rows converge locally uniformly, bounded by a constant times the summable intensity rows. Finally $1-e^{-\beta_c J}\leq\beta_c J$ gives the displayed flux bound.</p>
<p>This supplies the finite positive endpoint, subcritical finiteness and boundary-flux assumptions used later in this article. If the matching upper bound on $J$ and the stated rooted damping estimate are also supplied, <a href="/tag/7YNX/">the conditional two-point theorem</a> therefore applies at $b=\beta_c$. Rooted damping is a separate input to this argument, supplied by <a href="/tag/12NL/">the marked-tree splitting proof</a> for independent bonds. Nor does finite critical intensity alone prove absence of an infinite critical cluster.</p>

## The sibling-block expected-size recursion {#section-expected-size}

<a id="tag-655W" data-assertion="theorem" data-title="Restricted hierarchical susceptibility bound from rooted damping"></a>
<p>Retain the model of <a href="/tag/7AER/">the amplification theorem</a> and the endpoint hypotheses of <a href="/tag/2XJX/">the quantile bound</a>: $0\leq a&lt;b&lt;\infty$, $b&gt;0$, and $\chi(\beta)&lt;\infty$ for every $\beta\in(a,b)$. Let $a_n=\mathbb E_b|K_o^{\Lambda_n}|$ be the expected root-cluster size using only edges inside its level-$n$ block. Suppose the following rooted damping estimate holds in each finite block, with its largest-cluster quantile $R_n=R_n(b)$:</p>
<div class="math-display">$$\mathbb P_b(|K_x^{\Lambda_n}|\geq\lambda R_n)\leq e^{1-\lambda/9}\mathbb P_b(|K_x^{\Lambda_n}|\geq R_n)\qquad(x\in\Lambda_n,\ \lambda\geq1).$$</div>
<p>There are constants $k,C'&gt;0$, independent of $n$, such that</p>
<div class="math-display">$$a_{n+1}\geq kL^{-\alpha n}a_n^2,\qquad a_n\leq C'L^{\alpha n}\qquad(n\geq0).$$</div>
<p>Rooted damping is the <a href="/tag/21D4/">universal-tightness input</a>; it is stated here for block-restricted clusters and follows from <a href="/tag/12NL/">the finite-witness proof</a> applied to the block as the whole graph. No lower bound on $a_n$ is asserted.</p>
<p><em>Proof.</em> Choose a fixed real $t\geq1$ with $(t+9)e^{1-t/9}\leq1/2$. If $X$ is a rooted cluster size in a level-$n$ block and $R=R_n$, tail integration and rooted damping give</p>
<div class="math-display">$$\begin{aligned}
\mathbb E[X\mathbf1_{\{X&gt;tR\}}]
&=tR\,\mathbb P(X&gt;tR)+\int_{tR}^\infty\mathbb P(X&gt;s)\,ds\\
&\leq(t+9)R e^{1-t/9}\mathbb P(X\geq R)
\leq\frac12\mathbb E X.
\end{aligned}$$</div>
<p>Thus truncation to $X\leq tR$ retains at least half the mean. This is a relative-mean estimate; a small probability of exceeding $tR$ alone would not suffice.</p>
<p>Choose a sibling level-$n$ block $\Lambda_n'$ inside the parent of $\Lambda_n$. Condition on the two block interiors. Let $X=|K_o^{\Lambda_n}|$, and let $C_i$ be the clusters in $\Lambda_n'$. Every edge between the two blocks has weight at least $cL^{-(d+\alpha)(n+1)}$. With $\lambda_n=bcL^{-(d+\alpha)(n+1)}$, the conditional probability that $K_o^{\Lambda_n}$ has a direct edge to $C_i$ is at least $1-e^{-\lambda_n X|C_i|}$. Therefore</p>
<div class="math-display">$$a_{n+1}\geq\mathbb E\sum_i |C_i|\bigl(1-e^{-\lambda_n X|C_i|}\bigr).$$</div>
<p>The selected sibling clusters are disjoint, so this counts each of their vertices at most once. It does not require the different connecting events to be independent.</p>
<p>Restrict the sum to $X\leq tR_n$ and $|C_i|\leq tR_n$. The quantile bound $R_n^2\leq(A/b)L^{(d+\alpha)n}$ makes $\lambda_n X|C_i|\leq T$, where $T=cAt^2L^{-(d+\alpha)}$ is independent of $n$. Since $1-e^{-u}\geq ue^{-T}$ for $0\leq u\leq T$, independence of the block interiors gives</p>
<div class="math-display">$$a_{n+1}\geq e^{-T}\lambda_n\,\mathbb E[X\mathbf1_{\{X\leq tR_n\}}]\,\mathbb E\sum_i|C_i|^2\mathbf1_{\{|C_i|\leq tR_n\}}.$$</div>
<p>Counting each sibling vertex in its own cluster rewrites the last sum as $\sum_{x\in\Lambda_n'}|K_x^{\Lambda_n'}|\mathbf1_{\{|K_x^{\Lambda_n'}|\leq tR_n\}}$. Translations within a hierarchical block preserve its restricted law, so the truncated-mean bound makes the two factors at least $a_n/2$ and $L^{dn}a_n/2$. Hence the recursion holds with</p>
<div class="math-display">$$k=\frac{bc}{4}e^{-T}L^{-(d+\alpha)}&gt;0.$$</div>
<p>To turn the lower recursion into an upper bound, put $y_n=kL^{-\alpha(n+1)}a_n$. Then $y_{n+1}\geq y_n^2$. If $y_n&gt;1$ at any scale, iteration gives $y_{n+j}\geq y_n^{2^j}$. But the deterministic volume bound $a_{n+j}\leq L^{d(n+j)}$ implies</p>
<div class="math-display">$$y_{n+j}\leq kL^{-\alpha}L^{(d-\alpha)(n+j)},$$</div>
<p>which grows only exponentially in $j$, a contradiction. Thus $y_n\leq1$ for every $n$, and $a_n\leq(L^\alpha/k)L^{\alpha n}$.</p>
<p>This supplies the sibling-block recursion and its deterministic runaway conclusion in the notes, lines 4140–4177. The constants need not be sharp. The sharpness boundary-flux lower bound, pointwise conversion and removal of the block restriction remain further steps.</p>

## From block means to the two-point function {#section-two-point}

<a id="tag-7YNX" data-assertion="theorem" data-title="Conditional hierarchical two-point bounds from block means and boundary flux"></a>
<p>Retain all hypotheses of <a href="/tag/655W/">the expected-size theorem</a>, including its general endpoint $b$ and rooted damping, and suppose also that for some $C_0&lt;\infty$,</p>
<div class="math-display">$$J(u,v)\leq C_0L^{-(d+\alpha)j}\quad\text{at hierarchical level }j.$$</div>
<p>Write $\tau_n(o,u)=\mathbb P_b(o\leftrightarrow u\text{ using only edges in }\Lambda_n)$ and $\tau(o,u)=\mathbb P_b(o\leftrightarrow u)$. Assume the boundary-flux inequalities</p>
<div class="math-display">$$b\sum_{u\in\Lambda_n}\tau_n(o,u)\sum_{v\notin\Lambda_n}J(u,v)\geq1\qquad(n\geq0).$$</div>
<p>Then there are constants $c_1,C_1&gt;0$ such that, whenever $x\in\Lambda_n\setminus\Lambda_{n-1}$ and $n\geq1$,</p>
<div class="math-display">$$c_1L^{-(d-\alpha)n}\leq\tau_n(o,x)\leq\tau(o,x)\leq C_1L^{-(d-\alpha)n}.$$</div>
<p>The boundary-flux inequalities and finite susceptibility below $b$ are the sharpness inputs to this conditional statement. The theorem does not establish those inputs or identify $b$ as the critical parameter.</p>
<p><em>Proof.</em> The number of vertices at hierarchical level $j$ from a fixed vertex is $(1-L^{-d})L^{dj}$. For every $u\in\Lambda_n$, all vertices outside $\Lambda_n$ are at levels greater than $n$, so</p>
<div class="math-display">$$\sum_{v\notin\Lambda_n}J(u,v)\leq D L^{-\alpha n},\qquad D=\frac{C_0(1-L^{-d})L^{-\alpha}}{1-L^{-\alpha}}.$$</div>
<p>The flux hypothesis therefore gives $a_n\geq L^{\alpha n}/(bD)$. Together with the preceding theorem this bounds the restricted mean above and below by fixed multiples of $L^{\alpha n}$.</p>
<p>For the pointwise lower bound, the two vertices $o,x$ lie in distinct level-$(n-1)$ blocks inside $\Lambda_n$. Their clusters in these two blocks are independent, with volumes $X,Y$ each having mean $a_{n-1}$. The same truncation used in the sibling recursion retains at least half of each mean below $tR_{n-1}$. On that event, with $\lambda=bcL^{-(d+\alpha)n}$, we have $\lambda XY\leq T=cAt^2L^{-(d+\alpha)}$. A direct edge between the clusters gives</p>
<div class="math-display">$$\tau_n(o,x)\geq e^{-T}\lambda\,\mathbb E[X\mathbf1_{\{X\leq tR_{n-1}\}}]\mathbb E[Y\mathbf1_{\{Y\leq tR_{n-1}\}}]\geq\frac{ce^{-T}L^{-2\alpha}}{4bD^2}L^{-(d-\alpha)n}.$$</div>
<p>This uses the lower block mean explicitly; an averaged estimate and distance symmetry alone would not supply this lower bound.</p>
<p>For the upper bound, let $E_m$ be the event that $o$ connects to $x$ inside $\Lambda_m$. Every finite open path is contained in some such block, and $E_m$ increases with $m$. Thus</p>
<div class="math-display">$$\tau(o,x)=\mathbb P(E_n)+\sum_{m&gt;n}\mathbb P(E_m\setminus E_{m-1}).$$</div>
<p>On $E_n$, any path from $o$ to $x$ crosses between level-$(n-1)$ child blocks. On $E_m\setminus E_{m-1}$, every path inside $\Lambda_m$ must cross between level-$(m-1)$ child blocks. In either case choose a simple witnessing path and orient one such edge $(u,v)$ along it. The two path segments and that edge have pairwise disjoint edge sets. Finite-coordinate BK and a union bound over oriented crossing pairs give, for the corresponding term at level $m$,</p>
<div class="math-display">$$\mathbb P(\text{term at level }m)\leq\sum_{\substack{u,v\in\Lambda_m\\u,v\text{ in different children}}}\tau_m(o,u)\bigl(1-e^{-bJ(u,v)}\bigr)\tau_m(v,x)\leq bC_0L^{-(d+\alpha)m}a_m^2.$$</div>
<p>Translations within $\Lambda_m$ make both connection sums equal to $a_m$, and $1-e^{-bJ}\leq bJ$. With $a_m\leq C'L^{\alpha m}$, this is at most $bC_0(C')^2L^{-(d-\alpha)m}$. Since $\alpha&lt;d$, summing the geometric series gives the upper bound with</p>
<div class="math-display">$$C_1=\frac{bC_0(C')^2}{1-L^{-(d-\alpha)}}.$$</div>
<p>The two path pieces are both estimated in the larger block $\Lambda_m$; neither is assumed to stay in the original scale-$n$ block. Their resulting decay in the excess scale is enough for summability.</p>
<p>This supplies the boundary-flux reduction and restricted-to-unrestricted argument in the notes, lines 4178–4263. It completes the two-point proof mechanism conditional on the stated sharpness and rooted-damping inputs. The hierarchical volume-tail benchmarks, including critical-dimensional logarithms, require additional results.</p>

## The triangle diagram across scales {#section-triangle}

<a id="tag-MS6M" data-assertion="theorem" data-title="Hierarchical triangle threshold from two-sided kernel bounds"></a>
<p>On the standard hierarchical lattice with $L\geq2$, $d\geq1$, let $0&lt;\alpha&lt;d$ and let $f$ be a nonnegative function satisfying, for constants $0&lt;c\leq C&lt;\infty$,</p>
<div class="math-display">$$c\langle x\rangle^{-(d-\alpha)}\leq f(x)\leq C\langle x\rangle^{-(d-\alpha)},\qquad \langle x\rangle=\max\{1,\|x\|\}.$$</div>
<p>Define</p>
<div class="math-display">$$\Delta_N=\sum_{x,y\in\Lambda_N}f(x)f(y-x)f(y),\qquad N\geq0.$$</div>
<p>There are positive constants $a,A$, depending only on $c,C,L,d,\alpha$, such that for every integer $n\geq1$,</p>
<div class="math-display">$$aL^{(3\alpha-d)n}\leq\Delta_n-\Delta_{n-1}\leq AL^{(3\alpha-d)n}.$$</div>
<p>Consequently the full triangle sum is finite exactly when $3\alpha&lt;d$. For $3\alpha=d$, $\Delta_N\asymp N+1$; for $3\alpha&gt;d$, $\Delta_N\asymp L^{(3\alpha-d)N}$. These are deterministic kernel statements; neither positive definiteness nor a radial equality for $f$ is required.</p>
<p><em>Proof.</em> Put $s=d-\alpha$ and $F_n=\sum_{z\in\Lambda_n}f(z)$. Shell counting gives</p>
<div class="math-display">$$cL^{\alpha n}\leq F_n\leq C\sum_{j=0}^nL^{\alpha j}\leq\frac{C}{1-L^{-\alpha}}L^{\alpha n}.$$</div>
<p>For the lower bound, use $f(z)\geq cL^{-sn}$ throughout $\Lambda_n$. For the upper bound, a level-$j$ shell has at most $L^{dj}$ vertices; the $j=0$ term accounts for the origin.</p>
<p>The increment contains precisely those pairs $(x,y)$ in $\Lambda_n^2$ for which at least one vertex is outside $\Lambda_{n-1}$. Among the three distances $\|x\|,\|y\|,\|y-x\|$, at least two then equal $L^n$: the ultrametric inequality excludes a unique largest distance. Cover these pairs by the three possible choices of two such distances. The corresponding two factors are at most $C^2L^{-2sn}$. In each case, the sum of the remaining factor over all pairs in $\Lambda_n^2$ is $L^{dn}F_n$. For the factor $f(y-x)$ this follows by setting $z=y-x$ in the finite subgroup $\Lambda_n$; the other two cases are immediate. Overcounting is harmless, so</p>
<div class="math-display">$$\Delta_n-\Delta_{n-1}\leq3C^2L^{-2sn}L^{dn}F_n\leq\frac{3C^3}{1-L^{-\alpha}}L^{(3\alpha-d)n}.$$</div>
<p>For the reverse inequality restrict to $x\in\Lambda_n\setminus\Lambda_{n-1}$ and $y\in\Lambda_{n-1}$. Both $x$ and $y-x$ have norm $L^n$. There are $(1-L^{-d})L^{dn}$ choices of $x$, whence</p>
<div class="math-display">$$\Delta_n-\Delta_{n-1}\geq c^2L^{-2sn}(1-L^{-d})L^{dn}F_{n-1}\geq c^3(1-L^{-d})L^{-\alpha}L^{(3\alpha-d)n}.$$</div>
<p>Summing the increments, starting from $\Delta_0=f(0)^3$, proves all three cases. The full sum is their monotone limit.</p>
<p>Applied to the preceding conditional two-point bounds, this locates the triangle threshold without assuming radial symmetry. At $3\alpha=d$, the linear growth in the number of scales is logarithmic in the block radius $L^N$. This does not by itself prove logarithmic corrections for cluster volumes, susceptibility, or the percolation density; those require additional probabilistic arguments.</p>

## A constraint on the volume-tail exponent {#section-volume-exponent}

<a id="tag-7GDE" data-assertion="corollary" data-title="Hierarchical volume-tail exponent obstruction below the triangle threshold"></a>
<p>In the model of <a href="/tag/7AER/">the amplification theorem</a>, suppose the weights are symmetric and also satisfy $J(u,v)\leq C_0L^{-(d+\alpha)j}$ at level $j$, for some finite $C_0$. Assume $d/3&lt;\alpha&lt;d$. If the critical full-cluster tail has a finite positive logarithmic exponent $\delta$, in the sense that</p>
<div class="math-display">$$\mathbb P_{\beta_c}(|K_o|\geq n)=n^{-1/\delta+o(1)}\qquad(n\to\infty),$$</div>
<p>then</p>
<div class="math-display">$$\delta\geq\frac{d+\alpha}{d-\alpha}.$$</div>
<p><em>Proof.</em> The upper weight bound is summable because $\alpha&gt;0$. Thus <a href="/tag/FF30/">the critical-intensity theorem</a> gives a finite positive $\beta_c$, the critical quantile estimate and boundary flux. The <a href="/tag/12NL/">rooted-tail theorem</a> supplies damping in each finite block. Consequently <a href="/tag/7YNX/">the two-point argument</a> applies at $b=\beta_c$; its boundary-flux calculation gives $\mathbb E_{\beta_c}|K_o^{\Lambda_m}|\geq c_*L^{\alpha m}$ for a fixed $c_*&gt;0$.</p>
<p>If the asserted inequality for $\delta$ failed, we could choose</p>
<div class="math-display">$$\frac{d-\alpha}{d+\alpha}&lt;\theta&lt;\min\{1/\delta,1/2\},$$</div>
<p>since $\alpha&gt;d/3$. The logarithmic tail law gives $\mathbb P_{\beta_c}(|K_o|\geq n)\leq A n^{-\theta}$ for all integers $n\geq1$, after enlarging $A$ for finitely many small values. Translation invariance gives the same bound at every root. Apply <a href="/tag/UVQ6/">finite-window hyperscaling</a> to $\Lambda_m$, and use that an internal cluster is contained in the full-cluster intersection:</p>
<div class="math-display">$$
c_*L^{\alpha m}\leq\mathbb E_{\beta_c}|K_o^{\Lambda_m}|
\leq\sum_{v\in\Lambda_m}\mathbb P_{\beta_c}(o\leftrightarrow v)
\leq C A^{2/(1+\theta)}L^{d(1-\theta)m/(1+\theta)}.
$$</div>
<p>The last exponent is smaller than $\alpha$ by the choice of $\theta$, a contradiction as $m\to\infty$.</p>
<p>This is the volume-exponent obstruction of <a href="https://arxiv.org/pdf/2103.17013v1#page=6">Corollary 1.5</a>, with the underlying probability bound proved separately. It does not establish existence of $\delta$, equality in the bound, or any logarithmic correction. Radial equality of the weights is unnecessary for this argument; the stated translation invariance and two-sided level bounds suffice.</p>

## Boundary scales below an endpoint {#section-boundary-scales}

<p>Fix integers $L\geq2$, $d\geq1$ and a real $0&lt;\alpha&lt;d$. On $\mathbb H_L^d$, let $J$ be a symmetric displacement kernel satisfying</p>
<div class="math-display">$$c_J\|x\|^{-d-\alpha}\leq J(x)\leq C_J\|x\|^{-d-\alpha}\qquad(x\ne0),$$</div>
<p>with $0&lt;c_J\leq C_J&lt;\infty$. Use the independent bond law with probabilities $q_\beta(x,y)=1-e^{-\beta J(y-x)}$. Write $\chi_n(\beta)=\mathbb E_\beta|K_o^{\Lambda_n}|$ for the internal-ball susceptibility, $\chi(\beta)=\mathbb E_\beta|K_o|$ for the full susceptibility, and $\tau_\beta$ for the full connection kernel. Suppose a finite $b&gt;0$ satisfies the two endpoint conditions</p>
<div class="math-display">$$\tau_b(o,x)\leq A\langle x\rangle^{-d+\alpha}\quad(x\in\mathbb H_L^d),\qquad
\varphi_b(\Lambda_n)\geq1\quad(n\geq0),$$</div>
<p>for some finite $A$. Here $\varphi_\beta(\Lambda_n)=\sum_{x\in\Lambda_n,y\notin\Lambda_n}\tau_\beta^{\Lambda_n}(o,x)q_\beta(x,y)$, with the first connection restricted to the ball. These are explicit inputs for the remainder of this section. At $b=\beta_c$ they are supplied by the upper critical two-point estimate and the root-containing finite-set criterion; a pointwise estimate alone does not supply the second condition.</p>

<a id="tag-GPDF" data-assertion="definition" data-title="Hierarchical boundary thresholds and their length scale"></a>
<p>Set</p>
<div class="math-display">$$r_n(\beta)=\sum_{y\notin\Lambda_n}(1-e^{-\beta J(y)}),\qquad
\varphi_\beta(\Lambda_n)=r_n(\beta)\chi_n(\beta).$$</div>
<p>The identity holds because translating by any $x\in\Lambda_n$ permutes its complement. Let $\beta_n\in(0,b)$ be the unique solution of $\varphi_{\beta_n}(\Lambda_n)=1/2$, and put</p>
<div class="math-display">$$b_n=\max_{0\leq k\leq n}\beta_k,\qquad
m(\beta)=\min\{n\geq0:\beta\leq b_n\},\qquad
\xi(\beta)=L^{m(\beta)}.$$</div>
<p>If the set defining $m(\beta)$ is empty, take $m(\beta)=\xi(\beta)=\infty$. The thresholds exist: $r_n$ is continuous on $[0,b]$ by domination by $bJ$, and strictly increasing; $\chi_n$ is continuous and nondecreasing, and is at least one. Thus their product is continuous and strictly increasing, starts at zero and is at least one at $b$.</p>

<a id="tag-6F2J" data-assertion="proposition" data-title="Finite-ball control at the hierarchical boundary thresholds"></a>
<p>Under the preceding assumptions, $\chi(\beta)\leq2\chi_n(\beta)$ whenever $0\leq\beta\leq\beta_n$. There are constants $c_0,C_0&gt;0$, independent of $n$ and $\beta$, such that</p>
<div class="math-display">$$c_0L^{\alpha n}\leq\chi_n(\beta)\leq\chi_n(b)\leq C_0L^{\alpha n}
\qquad(b_n\leq\beta\leq b).$$</div>
<p>If $b_n\leq\beta\leq b_{n+1}$, then also $\chi(\beta)\leq2C_0L^\alpha L^{\alpha n}$.</p>
<p><em>Proof.</em> The first estimate is a first-exit bound in a finite volume, where rearrangement is legitimate. For $N\geq n$, split a simple path in $\Lambda_N$ at its first exit from $\Lambda_n$. The internal path, exit edge and remaining path have disjoint edge witnesses. BK, a union bound and translation invariance within $\Lambda_N$ give</p>
<div class="math-display">$$\chi_N(\beta)\leq\chi_n(\beta)+\varphi_\beta(\Lambda_n)\chi_N(\beta).$$</div>
<p>The boundary sum may include vertices outside $\Lambda_N$; enlarging it only increases the right side. If $\beta\leq\beta_n$, its coefficient is at most $1/2$, so $\chi_N(\beta)\leq2\chi_n(\beta)$. Internal connection events increase to full connection events as $N\to\infty$, since each path is finite. Monotone convergence proves the full susceptibility bound without assuming it finite in advance.</p>
<p>Shell summation of the endpoint upper bound gives $\chi_n(b)\leq C_0L^{\alpha n}$. Also</p>
<div class="math-display">$$r_n(\beta)\leq b\sum_{y\notin\Lambda_n}J(y)\leq D L^{-\alpha n},\qquad
D=\frac{bC_J(1-L^{-d})}{L^\alpha-1}.$$</div>
<p>For $\beta\geq b_n\geq\beta_n$, the boundary coefficient is at least $1/2$, so $\chi_n(\beta)\geq(2D)^{-1}L^{\alpha n}$. Finally, if $\beta\leq b_{n+1}$, some $k\leq n+1$ attains that maximum. The first estimate at $k$ gives $\chi(\beta)\leq2\chi_k(b)\leq2C_0L^{\alpha(n+1)}$.</p>

## The rate of approach to the endpoint {#section-off-critical}

<a id="tag-OVWJ" data-assertion="theorem" data-title="Hierarchical susceptibility and length bounds from endpoint inputs"></a>
<p>Retain the model and both endpoint conditions of <a href="#section-boundary-scales">the boundary-scale section</a>, and assume $\alpha&lt;2d/5$. Then $b_n\uparrow b$, $\xi(\beta)&lt;\infty$ for $0\leq\beta&lt;b$, and</p>
<div class="math-display">$$\chi(\beta)\asymp\xi(\beta)^\alpha\qquad(\beta\uparrow b).$$</div>
<p>With $\varepsilon=b-\beta$, the upper bounds are</p>
<div class="math-display">$$\begin{array}{c|c|c}
\text{range}&\xi(b-\varepsilon)&\chi(b-\varepsilon)\\ \hline
0&lt;\alpha&lt;d/3&O(\varepsilon^{-1/\alpha})&O(\varepsilon^{-1})\\
\alpha=d/3&O(\varepsilon^{-1/\alpha}(\log(1/\varepsilon))^{2/\alpha})
&O(\varepsilon^{-1}(\log(1/\varepsilon))^2)\\
d/3&lt;\alpha&lt;2d/5&O(\varepsilon^{-1/(2d-5\alpha)})
&O(\varepsilon^{-\alpha/(2d-5\alpha)}).
\end{array}$$</div>
<p>All constants are independent of sufficiently small $\varepsilon&gt;0$. If $R=\sum_{x\ne0}J(x)$, then also $\chi(b-\varepsilon)\geq1/(R\varepsilon)$, so $\xi(b-\varepsilon)\geq c\varepsilon^{-1/\alpha}$ near $b$. These conclusions do not presuppose that $b$ has been identified as the critical parameter.</p>
<p><em>Proof.</em> Let $\Delta_n(\beta)$ be the triangle diagram of the internal connection kernel on $\Lambda_n$. The endpoint upper bound and the upper shell estimate in <a href="/tag/MS6M/">MS6M</a> imply, uniformly for $0\leq\beta\leq b$,</p>
<div class="math-display">$$1\leq\Delta_n(\beta)\leq C_1 H_n,\qquad
H_n=\begin{cases}1,&3\alpha&lt;d,\\ n+1,&3\alpha=d,\\
L^{(3\alpha-d)n},&3\alpha&gt;d.\end{cases}$$</div>
<p>Indeed, the internal kernel is bounded by the full endpoint kernel, which is bounded by $A\langle x-y\rangle^{-d+\alpha}$; apply that deterministic estimate to this last function. Since $\alpha&lt;2d/5&lt;d/2$, $H_n=o(L^{\alpha n})$. The preceding lemma therefore gives $\Delta_n(\beta)\leq\chi_n(\beta)/2$ for all sufficiently large $n$, uniformly on $b_n\leq\beta\leq b$.</p>
<p>Each ball is a finite group under translation, so its invariant law has the mass-transport property and finite susceptibility. To use <a href="/tag/4KBG/">the corrected quadratic inequality</a> without a normalization assumption, set $\kappa=\max(1,R)$ and apply it to weights $J/\kappa$ at parameter $t=\kappa\beta$. The chain rule supplies</p>
<div class="math-display">$$\chi_n'(\beta)\geq
\frac{(\chi_n(\beta)-\Delta_n(\beta))_+^2}
{3\kappa\beta^2\Delta_n(\beta)^2}
\geq c_1\frac{L^{2\alpha n}}{H_n^2}
\qquad(b_n\leq\beta\leq b)$$</div>
<p>almost everywhere, for all sufficiently large $n$. The finite internal row sum is positive when $n\geq1$ and at most $R$, as required after scaling. Integrating and using $\chi_n(b)\leq C_0L^{\alpha n}$ yields</p>
<div class="math-display">$$0&lt;b-b_n\leq C_2 H_n^2L^{-\alpha n}.$$
</div>
<p>The right side tends to zero: in the last regime its exponential rate is $2d-5\alpha&gt;0$. Thus $b_n\uparrow b$. Moreover each $b_n&lt;b$, so $m(\beta)\to\infty$ as $\beta\uparrow b$.</p>
<p>For $m=m(\beta)\geq1$, minimality gives $b_{m-1}&lt;\beta\leq b_m$. The preceding lemma at $m-1$, and at a maximizing index $k\leq m$, gives</p>
<div class="math-display">$$c_0L^{\alpha(m-1)}\leq\chi(\beta)\leq2C_0L^{\alpha m}.$$</div>
<p>This proves the comparison with $\xi^\alpha$. Also $\varepsilon&lt;b-b_{m-1}\leq C_2H_{m-1}^2L^{-\alpha(m-1)}$. In the first and third regimes this directly bounds $L^m$ by the stated power of $\varepsilon^{-1}$.</p>
<p>At $3\alpha=d$, it instead gives $\varepsilon\leq C_3m^2e^{-cm}$, where $c=\alpha\log L&gt;0$. Taking logarithms and using $2\log m\leq cm/2$ for large $m$ shows $m=O(\log(1/\varepsilon))$. Returning to the same inequality now gives $L^{\alpha m}\leq C_4\varepsilon^{-1}(\log(1/\varepsilon))^2$, proving the borderline bounds.</p>
<p>Finally $\varphi_b(\Lambda_n)\geq1$ and the bound on $r_n(b)$ force $\chi_n(b)\to\infty$, hence $\chi(b)=\infty$. If $R\varepsilon\chi(b-\varepsilon)&lt;1$, adding an independent intensity-$\varepsilon$ layer would keep susceptibility finite by <a href="/tag/MLLO/">MLLO</a>: its probability row sum is at most $R\varepsilon$. The union has the law at $b$, a contradiction. This proves the lower susceptibility bound and, by the comparison already established, the lower length bound.</p>
<p>The proof uses the squared positive part throughout. Its separation from the triangle diagram is proved before the derivative is bounded below by a multiple of $\chi_n^2/\Delta_n^2$.</p>

## Cluster tails and density {#section-off-critical-tails}

<a id="tag-WPAD" data-assertion="corollary" data-title="Hierarchical tail and density upper bounds near the triangle threshold"></a>
<p>Retain the model and both endpoint conditions of <a href="#section-boundary-scales">the boundary-scale section</a>. If $0&lt;\alpha&lt;4d/11$, the following bounds hold as $N\to\infty$ and $\varepsilon\downarrow0$:</p>
<div class="math-display">$$\begin{array}{c|c|c}
\text{range}&\mathbb P_b(|K_o|\geq N)&\mathbb P_{b+\varepsilon}(|K_o|=\infty)\\ \hline
0&lt;\alpha&lt;d/3&O(N^{-1/2})&O(\varepsilon)\\
\alpha=d/3&O(N^{-1/2}(\log N)^2)&O(\varepsilon(\log(1/\varepsilon))^2)\\
d/3&lt;\alpha&lt;4d/11&
O(N^{-(4d-11\alpha)/(4d-10\alpha)})&
O(\varepsilon^{(4d-11\alpha)/(2d-5\alpha)}).
\end{array}$$</div>
<p>In particular there is no infinite cluster at $b$.</p>
<p><em>Proof.</em> The weight row sum is finite. Apply <a href="/tag/X8T6/">the power-law susceptibility comparison</a> to OVWJ, with $(\gamma,a)=(1,0)$ below the triangle threshold, $(1,2)$ at the threshold, and $(\alpha/(2d-5\alpha),0)$ above it. In the last case $\gamma&lt;2$ is exactly $\alpha&lt;4d/11$, and $2-\gamma=(4d-11\alpha)/(2d-5\alpha)$.</p>
<p>For radial kernels, taking $b=\beta_c$ and using <a href="/tag/W498/">the critical two-point input</a> together with <a href="/tag/FF30/">the critical boundary-flux input</a> supplies the upper bounds in Theorems 1.9 and 4.1 of <a href="https://arxiv.org/html/2106.06400v3#S4">the triangle paper</a>. The arguments here prove the implications from those inputs. They do not improve the logarithmic powers, establish exponent limits or give matching lower tail and density estimates.</p>

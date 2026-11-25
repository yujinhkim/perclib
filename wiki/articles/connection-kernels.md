---
{
  "id": "connection-kernels",
  "title": "Connection kernels and triangle bounds",
  "subtitle": "Cluster positivity and finite matrix restrictions",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "The connection kernel is positive semidefinite. Finite restrictions give off-diagonal bounds, open-triangle decay and the first diagram comparison without an infinite-volume operator assumption.",
  "context": ["A random undirected graph on a nonempty countable set $V$.", "Every connection event is measurable; independence is not assumed.", "Connections use the full graph, with each vertex connected to itself."],
  "related": ["connectivity", "susceptibility", "triangle-condition"],
  "sourceIds": ["notes"],
  "aliases": ["positive semidefinite connection kernel", "cluster Gram representation", "off-diagonal triangle bound", "diagram comparison"],
  "prototypeUses": ["triangle-condition"]
}
---

## Positivity from the cluster partition {#section-positivity}

<p>Write $T(x,y)=\mathbb P(x\leftrightarrow y)$. Thus $T$ is symmetric, $0\leq T(x,y)\leq1$ and $T(x,x)=1$. These facts use only undirected connectivity, not a product law.</p>
<a id="tag-70KD" data-assertion="proposition" data-title="Positive semidefiniteness of the connection kernel"></a>
<p>For every finitely supported real family $(a_x)_{x\in V}$,</p>
<div class="math-display">$$\sum_{x,y\in V}a_xa_yT(x,y)=\mathbb E\!\left[\sum_C\left(\sum_{x\in C}a_x\right)^2\right]\geq0,$$</div>
<p>where $C$ ranges over the open clusters. Consequently every finite principal submatrix of $T$ is positive semidefinite.</p>
<p><em>Proof.</em> In each configuration, two vertices belong to the same cluster exactly when they are connected. Expanding the squares therefore gives</p>
<div class="math-display">$$\sum_C\left(\sum_{x\in C}a_x\right)^2=\sum_{x,y}a_xa_y\mathbf1_{\{x\leftrightarrow y\}}.$$</div>
<p>Only the finitely many clusters meeting the support of $a$ contribute. The right side is a finite sum of measurable random variables, so taking expectations proves the identity. In particular, no measurable enumeration of all clusters is needed.</p>

## Bounding open triangles {#section-triangles}

<p>Interpret all matrix sums as nonnegative sums, initially allowing infinity. Write</p>
<div class="math-display">$$T^2(x,y)=\sum_uT(x,u)T(u,y),\qquad T^3(x,y)=\sum_{u,v}T(x,u)T(u,v)T(v,y),\qquad \Delta_x=T^3(x,x).$$</div>
<p>The last expression is the rooted triangle diagram of <a href="/tag/67VP/">67VP</a>, here written for the present connection kernel.</p>
<a id="tag-UZ7J" data-assertion="proposition" data-title="Cubic connection bounds from finite diagonal triangles"></a>
<p>If $\Delta_x$ and $\Delta_y$ are finite, then</p>
<div class="math-display">$$T^3(x,y)\leq\sqrt{\Delta_x\Delta_y}&lt;\infty.$$</div>
<p>Also, for every $x$,</p>
<div class="math-display">$$\sum_uT(x,u)^2\leq\Delta_x,$$</div>
<p>as an inequality of nonnegative extended sums.</p>
<p><em>Proof.</em> For a finite set $F$ containing $x,y$, let $T_F=(T(u,v))_{u,v\in F}$. This is the restriction of the full connection kernel, not the kernel of the graph induced by $F$. By positivity, its eigenvalues are nonnegative, so $T_F^3$ is positive semidefinite. The Cauchy–Schwarz inequality for a positive semidefinite matrix gives</p>
<div class="math-display">$$\bigl(T_F^3(x,y)\bigr)^2\leq T_F^3(x,x)T_F^3(y,y).$$</div>
<p>Choose finite sets increasing to $V$. All entries of $T$ are nonnegative, so each of these cubic sums increases to its full counterpart. Passing to the limit proves the first claim, with a finite right side. For the second, retain just the terms $u=v$ in the defining double sum for $\Delta_x$ and use $T(u,u)=1$ and symmetry.</p>
<p>If a group acts transitively on $V$ and preserves $T$, then all $\Delta_x$ have the same value $\Delta$. Thus $\Delta&lt;\infty$ implies $T^3(x,y)\leq\Delta$ for every pair. This is a uniform bound, not a claim that $T^3(x,y)$ tends to zero when the vertices separate. The further argument giving open-triangle decay follows next.</p>

## Open-triangle decay {#section-localization}

<a id="tag-96A2" data-assertion="theorem" data-title="Open-triangle decay under a uniform triangle bound"></a>
<p>Suppose $D=\sup_x\Delta_x&lt;\infty$. For every fixed root $o$ and every $\varepsilon&gt;0$, there is a finite set $E\subseteq V$ such that</p>
<div class="math-display">$$T^3(o,x)&lt;\varepsilon\qquad(x\notin E).$$</div>
<p>If a group acts transitively on $V$, preserving both $T$ and a finite-valued metric $d$, then</p>
<div class="math-display">$$\lim_{r\to\infty}\ \sup_{d(u,v)\geq r}T^3(u,v)=0,$$</div>
<p>with the supremum of an empty set taken to be zero. In this case the uniform hypothesis is simply $\Delta_o&lt;\infty$ at one root.</p>
<p><em>Proof.</em> The quadratic bound above gives $\sum_vT(u,v)^2\leq D$ for every $u$. In particular $T(u,x)$ tends to zero outside finite sets. The same is true of $T^2(u,x)$: for a finite set $K$, Cauchy–Schwarz gives</p>
<div class="math-display">$$T^2(u,x)\leq\sum_{v\in K}T(u,v)T(v,x)+\sqrt D\left(\sum_{v\notin K}T(u,v)^2\right)^{1/2}.$$</div>
<p>First choose $K$ to make the second term small, then send $x$ outside a finite set to make every term in the finite sum small.</p>
<p>Fix $o$. For finite $F\subseteq V$, put</p>
<div class="math-display">$$R_F=\sum_{u,v\notin F}T(o,u)T(u,v)T(v,o).$$</div>
<p>As $F$ increases to $V$, $R_F\to0$, since this is a tail of the finite nonnegative sum $\Delta_o$. Positivity of $T$ yields the more useful one-sided tail estimate</p>
<div class="math-display">$$\sum_{u\notin F,\ v\in V}T(o,u)T(u,v)T(v,x)\leq\sqrt{R_F\Delta_x}\leq\sqrt{D R_F}.$$</div>
<p>To justify it, restrict to any finite set $H$ and apply Cauchy–Schwarz for the positive semidefinite matrix $T_H$ to the vectors $a_u=\mathbf1_{\{u\notin F\}}T(o,u)$ and $b_u=T(x,u)$, indexed by $H$. Their quadratic forms are bounded by $R_F$ and $\Delta_x$. Exhausting $V$ by $H$ proves the inequality by nonnegative summation; no bounded operator on $\ell^2(V)$ is assumed.</p>
<p>Splitting the first intermediate vertex according to membership in $F$ now gives</p>
<div class="math-display">$$T^3(o,x)\leq\sum_{u\in F}T(o,u)T^2(u,x)+\sqrt{D R_F}.$$</div>
<p>Choose $F$ to make the remainder less than $\varepsilon/2$. Each term in the finite sum tends to zero outside finite sets, so the sum is less than $\varepsilon/2$ outside a suitable finite set $E$. This proves the first claim. Under the transitive isometric action, every pair $(u,v)$ can be carried to $(o,x)$ with $d(o,x)=d(u,v)$. Choose $r$ larger than all distances from $o$ to points of $E$. The same bound then holds for every pair at distance at least $r$.</p>
<p>This supplies the decay of the three-link quantity in the notes' open-triangle localization input, lines 1458–1480. For a connected transitive graph one may take graph distance. No finite-susceptibility or unimodularity assumption is needed. If $T_\beta\leq T_{\beta_c}$ entrywise for $\beta\leq\beta_c$, the nonnegative cubic sums satisfy the same inequality, so a separation scale chosen at criticality also works uniformly below criticality. The subsequent cluster-coupling and path-surgery estimates are separate assertions.</p>

## The first diagram comparison {#section-comparison}

<a id="tag-C2YT" data-assertion="proposition" data-title="The first triangle-diagram comparison under a uniform diagonal bound"></a>
<p>Suppose $D=\sup_x\Delta_x&lt;\infty$. For a root $o$, define</p>
<div class="math-display">$$A_o=\sum_vT(o,v)T^2(o,v)T^3(o,v).$$</div>
<p>Then all the displayed kernel entries are finite and</p>
<div class="math-display">$$A_o\leq D\Delta_o\leq D^2.$$</div>
<p>In the transitive invariant case this gives $A_o\leq\Delta^2$.</p>
<p><em>Proof.</em> Retaining $v=y$ in the cubic sum shows $T^2(x,y)\leq T^3(x,y)$, since $T(y,y)=1$. The preceding bound therefore makes both entries finite and gives $T^3(o,v)\leq D$. Symmetry and rearrangement of nonnegative sums give</p>
<div class="math-display">$$A_o\leq D\sum_vT(o,v)T^2(o,v)=D\sum_{v,u}T(o,v)T(v,u)T(u,o)=D\Delta_o.$$</div>
<p>This is precisely the first half of the diagram comparison in the preliminary notes, lines 1931–1954, with $A$ defined at line 1841. The proof requires neither independent edges nor unimodularity. The comparison involving the notes' $B$ diagram is proved below under group invariance and finite susceptibility; those assumptions are not needed for the first comparison.</p>
<p>One sufficient condition for the uniform hypothesis is $\sup_x\sum_yT(x,y)\leq M&lt;\infty$. Indeed, $T(v,x)\leq1$ gives</p>
<div class="math-display">$$\Delta_x\leq\sum_uT(x,u)\sum_vT(u,v)\leq M^2.$$</div>
<p>This sufficient condition is stronger than the finite-triangle hypothesis and is not substituted for it. In particular, the finite-restriction argument above remains applicable when susceptibility is infinite but every diagonal triangle is finite with a uniform bound.</p>

## A finite matrix comparison {#section-matrix-comparison}

<p>For matrices of the same size, write $S\circ R$ for their entrywise product. This notation is distinct from ordinary matrix multiplication.</p>
<a id="tag-CS16" data-assertion="proposition" data-title="Entrywise comparison of powers of a positive semidefinite matrix"></a>
<p>If $S$ is a finite real symmetric positive semidefinite matrix, then</p>
<div class="math-display">$$S^2\circ S^2\preceq S\circ S^3,$$</div>
<p>where $\preceq$ denotes positive semidefinite order, not entrywise order.</p>
<p><em>Proof.</em> Choose an orthonormal eigenbasis $u_i$ with eigenvalues $\lambda_i\geq0$. Put $w_{ij}=u_i\circ u_j$, the vector of coordinatewise products. Expanding both matrix powers in this basis and pairing the terms indexed by $(i,j)$ and $(j,i)$ gives</p>
<div class="math-display">$$S\circ S^3-S^2\circ S^2=\frac12\sum_{i,j}\lambda_i\lambda_j(\lambda_i-\lambda_j)^2\,w_{ij}w_{ij}^{\mathsf T}.$$</div>
<p>Every summand is positive semidefinite. This proves the comparison without an entrywise positivity assumption on $S$.</p>

## The second diagram comparison on a group {#section-group-comparison}

<a id="tag-87W3" data-assertion="theorem" data-title="Second triangle-diagram comparison for a group-invariant connection kernel"></a>
<p>Suppose the vertex set is a countable group $G$, with identity $o$, and the connection kernel is invariant under simultaneous left translation:</p>
<div class="math-display">$$T(gx,gy)=T(x,y)\qquad(g,x,y\in G).$$</div>
<p>Assume $\chi=\sum_yT(o,y)&lt;\infty$. With $A_o$ as above, define</p>
<div class="math-display">$$B_o=\sum_v\bigl(T^2(o,v)\bigr)^3.$$</div>
<p>Then $B_o\leq A_o$. Combined with the first diagram comparison, this gives $B_o\leq A_o\leq\Delta_o^2$ under these assumptions.</p>
<p><em>Proof.</em> Translation invariance makes every row sum of $T$ equal to $\chi$, and symmetry gives the same column sums. For a finitely supported vector $f$, weighted Cauchy–Schwarz gives</p>
<div class="math-display">$$\sum_x\left|\sum_yT(x,y)f(y)\right|^2\leq\chi\sum_{x,y}T(x,y)|f(y)|^2=\chi^2\|f\|_2^2.$$</div>
<p>Thus $T$ extends to a bounded self-adjoint operator on $\ell^2(G)$. Its positivity follows from the cluster quadratic form. Nonnegative summation gives row sums $\chi^n$ for $T^n$. Since $T(x,y)\leq1$, it also gives $T^2(x,y)\leq\chi$ and $T^3(x,y)\leq\chi^2$.</p>
<p>Set $H=T\circ T^3-T^2\circ T^2$. Both entrywise products have row and column sums bounded by $\chi^3$, so their difference is a bounded self-adjoint operator by the same row-and-column estimate. To see that $H$ is positive, exhaust $G$ by finite sets $F$. Apply the finite matrix comparison to $T_F$. The entries of $T_F^2$ and $T_F^3$ converge to those of $T^2$ and $T^3$, respectively, by nonnegative summation. For every finitely supported $a$, the resulting finite quadratic forms therefore converge to $\langle a,Ha\rangle\geq0$. Boundedness extends this inequality to all of $\ell^2(G)$.</p>
<p>For a bounded matrix $M$ invariant under simultaneous left translation, define $\operatorname{tr}_o(M)=M(o,o)$. If $M,N$ are two such matrices, their product's diagonal series is absolutely convergent by Cauchy–Schwarz. Translation by $x^{-1}$ and reindexing give</p>
<div class="math-display">$$\begin{aligned}\operatorname{tr}_o(MN)&=\sum_x M(o,x)N(x,o)\\&=\sum_x M(x^{-1},o)N(o,x^{-1})=\operatorname{tr}_o(NM).\end{aligned}$$</div>
<p>All ordinary and entrywise products used here retain the invariance. Applying this trace identity with $M=HT$ and $N=T$ gives</p>
<div class="math-display">$$\operatorname{tr}_o(HT^2)=\operatorname{tr}_o(THT)=\langle T\delta_o,H T\delta_o\rangle\geq0.$$</div>
<p>By symmetry of $T^2$, the left side is exactly $A_o-B_o$. These sums are finite: each is at most $\chi^4$, using the row and pointwise bounds above. This proves $B_o\leq A_o$. Finally $\Delta_x\leq\chi^2$ for every $x$, and translation invariance makes the diagonal constant, so the first comparison applies.</p>
<p>This proves the second step of the notes' diagram comparison, lines 1972–2028, for countable groups with translation-invariant connection kernels and finite susceptibility. The source's more general unimodular-graph statement uses the invariant trace supplied below, under an explicit mass-transport assumption. Neither the finite matrix comparison nor positivity of $H$ asserts a pointwise inequality between their entries.</p>

## The unimodular trace {#section-unimodular}

<a id="tag-N0HM" data-assertion="definition" data-title="The mass-transport property of a transitive action"></a>
<p>Let a group $\Gamma$ act transitively on the countable vertex set $V$, and fix $o\in V$. The action has the mass-transport property if every diagonally invariant function $F:V\times V\to[0,\infty]$, meaning $F(gx,gy)=F(x,y)$, satisfies</p>
<div class="math-display">$$\sum_{v\in V}F(o,v)=\sum_{v\in V}F(v,o).$$</div>
<p>The sums may be infinite. This is the form of unimodularity used below. It is an additional assumption on the action; transitivity alone does not imply it.</p>

<a id="tag-IZAO" data-assertion="theorem" data-title="Triangle-diagram comparison under the mass-transport property"></a>
<p>Suppose the connection kernel $T$ is invariant under a transitive action with the mass-transport property, and $\chi=\sum_vT(o,v)&lt;\infty$. With</p>
<div class="math-display">$$\Delta=T^3(o,o),\qquad A=\sum_vT(o,v)T^2(v,o)T^3(o,v),\qquad B=\sum_v\bigl(T^2(o,v)\bigr)^3,$$</div>
<p>one has $B\leq A\leq\Delta^2$.</p>
<p><em>Proof.</em> Invariance and transitivity make all row sums of $T$ equal to $\chi$. The row-and-column estimate and finite principal-matrix argument used above therefore apply unchanged: $T$ is a bounded positive operator, and $H=T\circ T^3-T^2\circ T^2$ is bounded and positive. Those arguments use neither a group structure on $V$ nor a trace.</p>
<p>For invariant bounded real operators $M,N$, the series $\sum_vM(o,v)N(v,o)$ is absolutely convergent by Cauchy–Schwarz on the square-summable row and column. The function $F(x,y)=M(x,y)N(y,x)$ is diagonally invariant. Apply mass transport to its positive and negative parts; absolute convergence allows subtraction and gives</p>
<div class="math-display">$$\operatorname{tr}_o(MN)=\sum_vM(o,v)N(v,o)=\sum_vM(v,o)N(o,v)=\operatorname{tr}_o(NM).$$</div>
<p>Ordinary and entrywise products retain invariance. Taking $M=HT$ and $N=T$ now gives</p>
<div class="math-display">$$A-B=\operatorname{tr}_o(HT^2)=\operatorname{tr}_o(THT)=\langle T\delta_o,H T\delta_o\rangle\geq0.$$</div>
<p>The series defining $A$ and $B$ are finite by the same $\chi^4$ bounds as in the group case. Transitivity also makes the diagonal triangle constant, so the first comparison gives $A\leq\Delta^2$.</p>
<p>This supplies S012 of the notes under an explicit mass-transport hypothesis. The regular action of a countable group is the earlier special case, where inversion gives the trace identity directly. Independence of bonds is unnecessary for this diagram comparison; the connection kernel's positivity comes from the cluster partition.</p>

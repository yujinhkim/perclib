---
{
  "id": "spatial-cutoff-moments",
  "title": "Spatial moments under a soft cutoff",
  "subtitle": "Cutoff differentiation, displacement kernels and spatial diagrams",
  "kind": "method",
  "category": "Critical phenomena",
  "summary": "Cutoff differentiation controls spatial scales. Probability resolvents supply the tree diagrams; rescaling to Green kernels and compact-test bounds support the conditional canonical limit.",
  "context": [
    "Independent translation-invariant bonds on $\\mathbb Z^d$, with symmetric nonnegative off-diagonal intensities.",
    "Projected second moments and susceptibility are finite on the interval where differentiation is asserted.",
    "High-dimensional factorization errors and superprocess convergence are separate inputs."
  ],
  "related": [
    "cutoff-families",
    "integrated-susceptibility",
    "multipoint-trees",
    "marginal-ode",
    "size-biased-laws"
  ],
  "sourceIds": [
    "notes",
    "hutchcroft-lrp-1"
  ],
  "aliases": [
    "soft cutoff",
    "spatial moment",
    "radius of gyration",
    "cutoff derivative",
    "Brownian scaling",
    "stable scaling"
  ],
  "prototypeUses": []
}
---

## A cutoff that stays below the full model {#section-cutoff}

<a id="tag-0CUF" data-assertion="proposition" data-title="Strict domination and finite spatial moments for a soft power-law cutoff"></a>
<p>Fix $d\geq1$, $\alpha&gt;0$, $p=d+\alpha$, and put $\rho(y)=\|y\|_2$ for $y\in\mathbb Z^d\setminus\{0\}$. For $r\geq1$, define</p>
<div class="math-display">$$J_\infty(y)=\frac{\rho(y)^{-p}}p,\qquad J_r(y)=\mathbf1_{\{\rho(y)\leq r\}}\int_{\rho(y)}^r s^{-p-1}\,ds.$$</div>
<p>Then</p>
<div class="math-display">$$J_r(y)=J_\infty(y)\left(1-\left(\frac{\rho(y)}r\right)^p\right)_+,\qquad 0\leq J_r(y)\leq(1-r^{-p})J_\infty(y),$$</div>
<p>and $r\mapsto J_r(y)$ is locally absolutely continuous with derivative $r^{-p-1}\mathbf1_{\{\rho(y)&lt;r\}}$ almost everywhere. Let $b&gt;0$, and suppose the full-kernel model with probabilities $1-e^{-\beta J_\infty(y)}$ has finite susceptibility for every $0\leq\beta&lt;b$. Then the cutoff model with probabilities $1-e^{-bJ_r(y)}$ has finite susceptibility and all cluster-volume moments for every finite $r$. For every $u\in\mathbb R^d$, its projected second spatial moment is finite and satisfies</p>
<div class="math-display">$$S_2(r;u)=\mathbb E_{b,r}\sum_{x\in K_0}\langle x,u\rangle^2\leq r^2\|u\|_2^2\,\mathbb E_{b,r}|K_0|^3&lt;\infty.$$</div>
<p><em>Proof.</em> Evaluate the integral. Since every nonzero lattice displacement has $\rho(y)\geq1$, its ratio to $J_\infty(y)$ is at most $1-r^{-p}$. At finite $r$, this is strictly less than one. Monotone coupling therefore bounds cutoff susceptibility by the full susceptibility at $b(1-r^{-p})&lt;b$. The <a href="/tag/Y84V/">transitive tree-graph moment bound</a> gives all finite volume moments. Each open cutoff edge has Euclidean length at most $r$. In a finite cluster, a simple path from the root to any vertex uses at most $|K_0|-1$ edges, so $\|x\|_2\leq r|K_0|$. Sum the resulting projection bound over the cluster. Differentiating the integral gives the stated a.e. derivative.</p>
<p>Changing the cutoff adds intensity to all displacements shorter than the current radius, not just to a shell of edges at that radius. The formula fixes the normalization explicitly. Finiteness below the full-model endpoint is an input, not a consequence of taking a finite-range cutoff.</p>

## A uniform susceptibility bootstrap {#section-susceptibility-bootstrap}

<a id="tag-7F5O" data-assertion="theorem" data-title="Quantitative cutoff susceptibility from subcritical finiteness and endpoint divergence"></a>
<p>Use the kernel $J_r$ of <a href="/tag/0CUF/">0CUF</a>, with $d&gt;3\alpha$ and $b&gt;0$. Let $\chi_{\beta,r}$ denote cutoff susceptibility at intensity $\beta$, and let $\chi_{\beta,\infty}$ denote susceptibility for $J_\infty$. Assume</p>
<div class="math-display">$$\chi_{\beta,\infty}&lt;\infty\quad(0\leq\beta&lt;b),\qquad\chi_{b,\infty}=\infty.$$</div>
<p>Then there is $R&lt;\infty$ such that, with $C=4\alpha/(b v_d)$,</p>
<div class="math-display">$$\chi_{\beta,r}\leq Cr^\alpha\qquad(b/2\leq\beta\leq b,\ r\geq R).$$</div>
<p>Moreover, for $\eta=\min\{1,d-3\alpha\}&gt;0$,</p>
<div class="math-display">$$\chi_{b,r}=\frac{\alpha}{b v_d}r^\alpha\bigl(1+O(r^{-\eta})\bigr).$$</div>
<p><em>Proof.</em> Every finite-radius cutoff at $\beta\leq b$ has finite susceptibility and all volume moments by 0CUF. Put $f_\beta(r)=\chi_{\beta,r}$ and $N_r=\#\{y\ne0:\|y\|_2&lt;r\}$. The <a href="/tag/NJF3/">first-moment deficit bound</a> and $\mathbb E|K_0|^3\leq3f_\beta^5$ give, for almost every sufficiently large $r$,</p>
<div class="math-display">$$f_\beta'=\beta r^{-d-\alpha-1}N_r f_\beta^2(1-e_\beta),\qquad 0\leq e_\beta\leq\min\left\{1,\frac{3f_\beta^3}{N_r}\right\}.$$</div>
<p>The functions $f_\beta$ are locally absolutely continuous. Choose $R$ so large that for every $r\geq R$, $N_r\geq(7/8)v_dr^d$ and $3C^3r^{3\alpha}/N_r\leq1/8$. This choice is independent of $\beta$. On any interval where $f_\beta(r)\leq Cr^\alpha$, it follows that</p>
<div class="math-display">$$\frac{f_\beta'(r)}{f_\beta(r)^2}\geq\frac34\beta v_d r^{-\alpha-1}\quad\text{a.e.}$$</div>
<p>Fix $b/2\leq\beta&lt;b$. Since $f_\beta\leq\chi_{\beta,\infty}&lt;\infty$, the set of $r\geq R$ with $f_\beta(r)&gt;Cr^\alpha$ is bounded. If nonempty, let $s$ be its supremum. Continuity gives $f_\beta(s)=Cs^\alpha$, and $f_\beta(r)\leq Cr^\alpha$ for $r\geq s$. Integrate the reciprocal differential inequality from $s$ to $T$ and let $T\to\infty$. The nonnegative limiting reciprocal can be discarded, giving</p>
<div class="math-display">$$\frac1{f_\beta(s)}\geq\frac{3\beta v_d}{4\alpha}s^{-\alpha},\qquad f_\beta(s)\leq\frac{4\alpha}{3\beta v_d}s^\alpha\leq\frac{8\alpha}{3b v_d}s^\alpha&lt;Cs^\alpha,$$</div>
<p>a contradiction. Thus no such radius exists. At each fixed $r$, monotone coupling and finite path witnesses give $\chi_{\beta,r}\uparrow\chi_{b,r}$ as $\beta\uparrow b$. This proves the uniform bound including the endpoint.</p>
<p>Consequently $e_b(r)=O(r^{3\alpha-d})$. The lattice count $N_r=v_dr^d+O(r^{d-1})$ now gives</p>
<div class="math-display">$$\frac{f_b'(r)}{f_b(r)^2}=b v_d r^{-\alpha-1}\bigl(1+O(r^{-\eta})\bigr)\quad\text{a.e.}$$</div>
<p>As $r\to\infty$, the cutoff kernels increase to $J_\infty$. Another monotone coupling and finite-witness argument, followed by Tonelli over connected vertices, gives $f_b(r)\uparrow\chi_{b,\infty}=\infty$. Integrating the last equation to infinity therefore yields</p>
<div class="math-display">$$\frac1{f_b(r)}=\frac{b v_d}{\alpha}r^{-\alpha}\bigl(1+O(r^{-\eta})\bigr).$$</div>
<p>Inverting proves the equivalent.</p>
<p>This supplies the first-moment bootstrap discussed in the <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L4621">notes</a>, for the kernel normalization fixed above. It uses continuity at the last crossing, not a derivative at that crossing. The endpoint assumptions remain explicit; neither sharpness nor endpoint divergence is proved here. Combined with <a href="/tag/Z11O/">Z11O</a>, they give the three spatial second-moment regimes for this model.</p>

## Closing the high-dimensional volume hierarchy {#section-volume-hierarchy}

<a id="tag-K3DB" data-assertion="theorem" data-title="All cutoff volume-moment asymptotics under the susceptibility endpoint assumptions"></a>
<p>Under the hypotheses of <a href="/tag/7F5O/">7F5O</a>, put $m_p(r)=\mathbb E_{b,r}|K_0|^p$ and $B=\alpha/(b v_d)$. There is a constant $A\in(0,\infty)$ such that, for every fixed integer $p\geq1$,</p>
<div class="math-display">$$m_p(r)\sim(2p-3)!!\,A^{p-1}B^{2-p}r^{(2p-1)\alpha}.$$</div>
<p>Equivalently, $m_p\sim(2p-3)!!(m_2/m_1)^{p-1}m_1$. The constant $A$ is the second-moment amplitude; it is not specified by the leading susceptibility coefficient.</p>
<p><em>Proof.</em> All cutoff moments are finite. Write $\chi=m_1$, $c=br^{-d-\alpha-1}$ and $a=cN_r$. By 7F5O, $\chi=Br^\alpha(1+O(r^{-\eta}))$ with $\eta=\min\{1,d-3\alpha\}&gt;0$. In particular, $a\chi=\alpha/r+O(r^{-1-\eta})$.</p>
<p>The exact second-moment equation and <a href="/tag/NJF3/">its deficit bound</a> give $m_2'=3a\chi m_2(1-e_2)$, where</p>
<div class="math-display">$$0\leq e_2\leq\frac{c m_4}{a\chi m_2}\leq1152\frac{\chi^3\log^2(2\chi)}{N_r}=O(r^{3\alpha-d}\log^2 r).$$</div>
<p>The second inequality is <a href="/tag/IXEZ/">IXEZ</a>. Consequently</p>
<div class="math-display">$$\left(\log\frac{m_2(r)}{r^{3\alpha}}\right)'=O(r^{-1-\eta})+O(r^{3\alpha-d-1}\log^2 r)\quad\text{a.e.}$$</div>
<p>Both terms are absolutely integrable at infinity. The logarithm thus has a finite real limit, which proves $m_2(r)\sim Ar^{3\alpha}$ with $0&lt;A&lt;\infty$.</p>
<p>Now suppose the claimed equivalents hold through order $p-1$, with $p\geq3$. Let $H_p$ be the product-moment expression in <a href="/tag/XXTP/">XXTP</a>. The interior term involving $m_2m_{p-1}$ gives $H_p\geq c_p a\chi^{2p}$ for some $c_p&gt;0$ at all large radii. This also holds for $p=3$, where that term is a positive multiple of $m_2^2$. The ordinary tree-graph bound gives $m_{p+2}\leq(2p+1)!!\chi^{2p+3}$. Therefore XXTP implies</p>
<div class="math-display">$$0\leq1-\frac{m_p'}{H_p}\leq C_p\frac{c\chi^{2p+3}}{a\chi^{2p}}=O_p(r^{3\alpha-d})\longrightarrow0.$$</div>
<p>Thus the $p$th equation is asymptotically closed without assuming the $p$th moment equivalent. The linear induction step proved in <a href="/tag/5O1G/">5O1G</a> applies: its forcing uses only the already known lower moments, and its positive gap is $(p-2)\alpha$. It gives the double-factorial coefficient at order $p$. Induction proves the result for every fixed order.</p>
<p>The logarithmic comparison is used only to start the induction at the second moment. Thereafter the lower-order forcing and the ordinary tree bound suffice. This provides an alternative to the sharper fourth-to-second moment estimate invoked in the <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L4758">notes</a>; that stronger estimate is not asserted as proved here. The endpoint assumptions of 7F5O and the strict inequality $d&gt;3\alpha$ remain essential hypotheses of this argument.</p>

## An exact spatial derivative {#section-derivative}

<a id="tag-57RX" data-assertion="theorem" data-title="Projected second-moment derivative for increasing intensity families"></a>
<p>Let $I$ be an open real interval. For each nonzero $y\in\mathbb Z^d$, let $k_t(y)=k_t(-y)\geq0$ be finite, nondecreasing and locally absolutely continuous in $t\in I$, and use independent bonds of probabilities $1-e^{-k_t(v-u)}$. Fix a linear projection $\ell(x)=\langle x,u\rangle$. On every compact interval $[a,b]\subset I$, assume there is a nonnegative envelope $A(y)$ such that, almost everywhere in $t$ and for every $y\ne0$,</p>
<div class="math-display">$$0\leq\dot k_t(y)\leq A(y),\qquad \sum_{y\ne0}A(y)\bigl(1+\ell(y)^2\bigr)&lt;\infty.$$</div>
<p>Suppose $\chi(t)=\sum_x\tau_t(0,x)$ and $S(t)=\sum_x\ell(x)^2\tau_t(0,x)$ are finite throughout $I$. Put $M_t=\sum_{y\ne0}\dot k_t(y)$ and $D_t=\sum_{y\ne0}\dot k_t(y)\ell(y)^2$. Then $S$ is locally Lipschitz and, almost everywhere,</p>
<div class="math-display">$$\begin{aligned}
S'(t)&=\sum_{y\ne0}\dot k_t(y)\,\mathbb E_t\!\left[\mathbf1_{\{0\not\leftrightarrow y\}}\sum_{x\in K_0}\sum_{z\in K_y}\ell(z-x)^2\right],\\
0\leq S'(t)&\leq2M_t\chi(t)S(t)+D_t\chi(t)^2.
\end{aligned}$$</div>
<p>The two clusters in the identity belong to the same configuration; they are not independent.</p>
<p><em>Proof.</em> Restrict the model to a finite vertex set $F$ containing zero. Differentiate the finite sum $S_F(t)=\sum_{z\in F}\ell(z)^2\tau_{F,t}(0,z)$. The derivative of an edge probability is $\dot k_t(v-u)e^{-k_t(v-u)}$, and pivotality is independent of that edge's state. Thus it is the closed-pivotal probability that carries the coefficient $\dot k_t(v-u)$. Orienting each pivotal edge towards the cluster containing $z$ gives</p>
<div class="math-display">$$S_F'(t)=\sum_{\substack{u,v\in F\\u\ne v}}\sum_{z\in F}\dot k_t(v-u)\ell(z)^2\mathbb P_{F,t}(0\leftrightarrow u,\ v\leftrightarrow z,\ 0\not\leftrightarrow v).$$</div>
<p>All coefficients are nonnegative. BK bounds the probability by $\tau_t(0,u)\tau_t(v,z)$ in the full model. With $y=v-u$ and $w=z-v$, the resulting sum is</p>
<div class="math-display">$$\sum_{u,y,w}\dot k_t(y)\tau_t(0,u)\tau_t(0,w)\ell(u+y+w)^2=2M_t\chi(t)S(t)+D_t\chi(t)^2.$$</div>
<p>Here $y\ne0$. Symmetry makes the first moments of each of the three weights vanish. Their absolute first moments are finite by Cauchy–Schwarz from the assumed zeroth and second moments, so expansion of the square and cancellation of its cross terms are justified.</p>
<p>On $[a,b]\subset I$, replace $\dot k_t$ by its envelope and the connection probabilities by those at $b$. The same calculation gives a finite bound uniform in $F,t$. Every fixed connection has a finite path witness. Under finite-volume exhaustion the distinct-cluster indicators in the derivative sum converge pointwise: a full connection eventually appears, while a full nonconnection persists. The preceding summable BK bound permits dominated convergence, both in the vertex sums and in the integral over $[a,b]$.</p>
<p>Integrate the finite identity before taking this limit. Since $S_F(t)\uparrow S(t)$, this gives an exact integral identity for $S$, with a bounded integrand on each compact interval. Hence $S$ is locally Lipschitz and its derivative equals that integrand almost everywhere. Finally translate each configuration by $-u$ and reindex $x=-u$, $y=v-u$, and $z$ as the translated target. The original target projection becomes $\ell(z-x)$, producing the displayed two-cluster identity.</p>
<p>For the soft cutoff above, take $k_r(y)=bJ_r(y)$. The envelope has finite support on every compact range of radii, and the preceding proposition supplies the required moments. With $B_r=\{y:\|y\|_2\leq r\}$, for almost every $r&gt;1$ the upper bound specializes to</p>
<div class="math-display">$$S_2'(r;u)\leq br^{-d-\alpha-1}\left[2(|B_r|-1)\chi_r S_2(r;u)+\chi_r^2\sum_{y\in B_r}\langle y,u\rangle^2\right].$$</div>
<p>The diagonal is excluded, accounting for $|B_r|-1$. The exact derivative is the same prefactor times the two-cluster sum over $y\in B_r\setminus\{0\}$. Replacing that sum by a product asymptotic with controlled errors is a further probabilistic estimate.</p>

## A spatially weighted tree-graph bound {#section-weighted-tree}

<a id="tag-5OBO" data-assertion="theorem" data-title="Cluster-volume moments with a projected spatial weight"></a>
<p>Consider a translation-invariant independent bond model on $\mathbb Z^d$. Fix $u\in\mathbb R^d$, put $\ell(x)=\langle x,u\rangle$, and assume</p>
<div class="math-display">$$\chi=\sum_x\tau(0,x)&lt;\infty,\qquad S=\sum_x\ell(x)^2\tau(0,x)&lt;\infty.$$</div>
<p>For every integer $m\geq1$,</p>
<div class="math-display">$$\mathbb E\!\left[|K_0|^{m-1}\sum_{x\in K_0}\ell(x)^2\right]\leq(2m-1)(2m-3)!!\,\chi^{2m-2}S,$$</div>
<p>where $(-1)!!=1$. No rotational symmetry or finite interaction range is required.</p>
<p><em>Proof.</em> Expand the expectation as a sum over $m$ ordered marked vertices, with weight $\ell(x_m)^2$ and joint connection probability for $0,x_1,\ldots,x_m$. Apply the <a href="/tag/AFH6/">multipoint tree-graph bound</a>. Each of its $(2m-3)!!$ shapes has $E=2m-1$ edges. Root the shape at the leaf fixed at zero and orient every edge away from it. Assigning a displacement $h_e\in\mathbb Z^d$ to each edge is a bijection with assigning positions to all its nonroot vertices. Translation invariance turns the product of connection factors into $\prod_e\tau(0,h_e)$.</p>
<p>If $P$ is the unique shape path from the root to the leaf labelled $x_m$, then $\ell(x_m)=\sum_{e\in P}\ell(h_e)$. The symmetric weight $\tau(0,h)=\tau(0,-h)$ has zero first projected moment; its absolute first moment is finite by Cauchy–Schwarz, bounded by $\sqrt{\chi S}$. Consequently expansion of the square in the diagram sum is justified, all cross terms vanish, and</p>
<div class="math-display">$$\sum_{(h_e)}\left(\sum_{e\in P}\ell(h_e)\right)^2\prod_e\tau(0,h_e)=|P|S\chi^{E-1}\leq(2m-1)S\chi^{2m-2}.$$</div>
<p>Sum over the shapes. The case $m=1$ is the identity defining $S$. Repeated marked vertices and zero edge displacements are included in the tree-graph bound and require no separate correction.</p>
<p>In particular, for any deterministic window $B$ containing the root,</p>
<div class="math-display">$$\mathbb E\!\left[|K_0|\,|K_0\cap B|\sum_{x\in K_0}\ell(x)^2\right]\leq15\chi^4S.$$</div>
<p>This follows from $|K_0\cap B|\leq|K_0|$ and the case $m=3$. For a cutoff family with $N_r\asymp r^d$, $\chi_r=O(r^\alpha)$ and $S_r&gt;0$, division by $N_r\chi_r S_r$ bounds this error ratio by $O(r^{3\alpha-d})$. When $d&gt;3\alpha$ this bound is integrable against $dr/r$ at infinity. If $S_r=0$, the weighted expectation itself is zero, and no division is needed.</p>
<p>This supplies the spatially weighted tree-graph estimate in the <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L5479">notes' spatial derivative calculation</a>. The following <a href="/tag/6DOC/">collision argument</a> supplies the domination of the derivative deficit by this weighted error.</p>

## Controlling the spatial derivative deficit {#section-spatial-deficit}

<a id="tag-6DOC" data-assertion="theorem" data-title="Spatial derivative error bounded by four-point collisions"></a>
<p>Under the hypotheses of <a href="/tag/57RX/">57RX</a>, suppose that for almost every parameter $t$ there are finite $R,c\geq0$ such that $w(y)=\dot k_t(y)\leq c\mathbf1_{\{\|y\|_2\leq R\}}$ for every $y\ne0$. At such a parameter write $K=K_0$, $W=\sum_{x\in K}\ell(x)^2$, $B_R=\{y:\|y\|_2\leq R\}$, $a=\sum_{y\ne0}w(y)$ and $D=\sum_{y\ne0}w(y)\ell(y)^2$. Then, almost everywhere,</p>
<div class="math-display">$$\begin{aligned}
0\leq 2a\chi S+D\chi^2-S'
&\leq6c\,\mathbb E[|K|\,|K\cap B_R|\,W]+3cR^2\|u\|_2^2\mathbb E[|K|^2|K\cap B_R|]\\
&\leq90c\chi^4S+9cR^2\|u\|_2^2\chi^5.
\end{aligned}$$</div>
<p><em>Proof.</em> Fix $x,y,z$ and let $A=\{0\leftrightarrow x\}$, $B=\{y\leftrightarrow z\}$. On $A\cap B\cap\{0\not\leftrightarrow y\}$ the two connections have disjoint witnesses. BK gives the first inequality below; Harris gives the second:</p>
<div class="math-display">$$\begin{aligned}
0\leq\delta(x,y,z)&:=\tau(0,x)\tau(y,z)-\mathbb P(A\cap B\cap\{0\not\leftrightarrow y\})\\
&\leq\mathbb P(A\cap B\cap\{0\leftrightarrow y\})
=\mathbb P(0,x,y,z\text{ lie in one cluster}).
\end{aligned}$$</div>
<p>The product diagram with weight $\ell(z-x)^2$ sums to $2a\chi S+D\chi^2$, by the symmetry calculation in 57RX. Subtracting its exact derivative identity therefore expresses the deficit as the nonnegative sum $\sum_{y\ne0,x,z}w(y)\delta(x,y,z)\ell(z-x)^2$. Both sums are finite, so this subtraction is legitimate.</p>
<p>Use $z-x=(z-y)+y-x$ and</p>
<div class="math-display">$$\ell(z-x)^2\leq3\bigl(\ell(z-y)^2+\ell(y)^2+\ell(x)^2\bigr).$$</div>
<p>After replacing $\delta$ by the four-point probability, the contribution with $\ell(x)^2$ is at most $c\mathbb E[|K|\,|K\cap B_R|\,W]$. Translation by $-y$, followed by the reindexing $(y,x,z)\mapsto(-y,z-y,x-y)$, gives the same bound for $\ell(z-y)^2$, since $w(y)=w(-y)$. The contribution with $\ell(y)^2$ is at most $cR^2\|u\|_2^2\mathbb E[|K|^2|K\cap B_R|]$. Multiplication by three proves the first upper bound. The <a href="/tag/5OBO/">weighted tree-graph bound</a> gives the first expectation at most $15\chi^4S$; the <a href="/tag/Y84V/">third-volume-moment bound</a> gives the second at most $\mathbb E|K|^3\leq3\chi^5$. This proves the final inequality.</p>
<p>For a soft cutoff, $w$ is constant on the nonzero displacements of length less than $r$, almost everywhere in $r$. Then $c/a=1/N_r$, where $N_r$ is their number. If $u\ne0$, lattice ball summation gives $D/a\asymp r^2\|u\|_2^2$ and $N_r\asymp r^d$. The last bound divided by $2a\chi S+D\chi^2$ is consequently $O(\chi^3/N_r)$. Thus an independently established estimate $\chi_r=O(r^\alpha)$ makes this relative error $O(r^{3\alpha-d})$, integrable against $dr/r$ when $d&gt;3\alpha$. For $u=0$ the spatial identity is identically zero. The lattice comparison follows by scaling the sums over the unit ball; its quadratic integral is positive for nonzero $u$.</p>
<p>This supplies the collision domination in the <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L5398">notes' second spatial moment derivative</a>, with explicit constants. The argument bounds the nonnegative deficit before expanding the square, so it does not assume that signed cross terms vanish under the dependent two-cluster law. Critical-dimensional improvements, precise coefficient asymptotics and convergence of embedded clusters still require additional estimates.</p>

## The spatial scales of the linear equation {#section-ode}

<a id="tag-GAF9" data-assertion="theorem" data-title="Three spatial-moment regimes for a linear equation with integrable coefficient error"></a>
<p>Let $r_0\geq1$, $\alpha,c&gt;0$, and let $S\geq0$ be locally absolutely continuous on $[r_0,\infty)$. Suppose almost everywhere</p>
<div class="math-display">$$S'(r)=\left(\frac{2\alpha}r+e(r)\right)S(r)+g(r),\qquad \int_{r_0}^\infty|e(r)|\,dr&lt;\infty,$$</div>
<p>where $g\geq0$ is locally integrable and $g(r)\sim cr^{\alpha+1}$. Then</p>
<div class="math-display">$$S(r)\sim\begin{cases}\dfrac{c}{2-\alpha}r^{\alpha+2},&amp;0&lt;\alpha&lt;2,\\cr^4\log r,&amp;\alpha=2,\\Kr^{2\alpha},&amp;\alpha&gt;2,\end{cases}$$</div>
<p>where $K\in(0,\infty)$ in the last case depends on the initial condition and the full coefficients. If additionally $m(r)\sim m_0r^\alpha$ with $m_0&gt;0$, the square root of $S(r)/m(r)$ has scale $r$, $r\sqrt{\log r}$, or $r^{\alpha/2}$ in the three respective regimes.</p>
<p><em>Proof.</em> Put $H(r)=r^{2\alpha}\exp(\int_{r_0}^r e(s)\,ds)$. The integral assumption gives $H(r)/r^{2\alpha}\to E\in(0,\infty)$, and variation of constants gives</p>
<div class="math-display">$$\frac{S(r)}{H(r)}=\frac{S(r_0)}{H(r_0)}+\int_{r_0}^r\frac{g(s)}{H(s)}\,ds,\qquad \frac{g(s)}{H(s)}\sim\frac cE s^{1-\alpha}.$$</div>
<p>For $\alpha&lt;2$ the integral is asymptotic to $c r^{2-\alpha}/(E(2-\alpha))$; for $\alpha=2$ it is asymptotic to $(c/E)\log r$. In both cases it dominates the initial term. For $\alpha&gt;2$ the integral converges, and its limit is positive because $g$ is eventually positive. Multiplication by $H$ proves the three assertions. Division by $m$ and taking a square root give the scale statements.</p>
<p>The integrable coefficient error is a real hypothesis. An estimate $e(r)=o(1/r)$ alone does not imply it: for $r&gt;1$, the error $1/(r\log r)$ contributes an extra factor $\log r$ to $H$. Thus a leading-order differential expression does not automatically justify an exact power-law amplitude in every regime.</p>

## Conditional spatial asymptotics for the normalized cutoff {#section-cutoff-asymptotics}

<a id="tag-Z11O" data-assertion="corollary" data-title="Spatial second-moment asymptotics from a quantitative cutoff susceptibility equivalent"></a>
<p>Use the Euclidean soft kernel $J_r$ of <a href="/tag/0CUF/">0CUF</a> at intensity $b&gt;0$. Assume $d&gt;3\alpha$, finite cutoff susceptibility at every finite radius, and, for some $\varepsilon&gt;0$,</p>
<div class="math-display">$$\chi_r=\frac{\alpha}{b v_d}r^\alpha\bigl(1+O(r^{-\varepsilon})\bigr),$$</div>
<p>where $v_d$ is the volume of the Euclidean unit ball. For $u\ne0$, put $c_u=\alpha^2\|u\|_2^2/[b v_d(d+2)]$. Then</p>
<div class="math-display">$$S_2(r;u)\sim\begin{cases}\dfrac{c_u}{2-\alpha}r^{\alpha+2},&amp;0&lt;\alpha&lt;2,\\c_u r^4\log r,&amp;\alpha=2,\\K_u r^{2\alpha},&amp;\alpha&gt;2,\end{cases}$$</div>
<p>with $K_u\in(0,\infty)$ in the last case. For $u=0$, $S_2(r;u)=0$ identically. The quantitative susceptibility equivalent is an input, not a conclusion of this corollary.</p>
<p><em>Proof.</em> Finiteness of susceptibility gives all volume moments by the tree-graph bound. The cutoff path-length estimate in 0CUF then gives finite spatial moments on every finite radius interval, so 57RX applies. Away from the countable set of lattice distances, write $c(r)=br^{-d-\alpha-1}$ and $N_r=\#\{y\ne0:\|y\|_2&lt;r\}$. Thus $a=cN_r$ and $D=c\sum_{\|y\|_2&lt;r}\langle y,u\rangle^2$.</p>
<p>Comparison with unit cubes gives</p>
<div class="math-display">$$N_r=v_dr^d+O(r^{d-1}),\qquad\sum_{\|y\|_2&lt;r}\langle y,u\rangle^2=\frac{v_d}{d+2}\|u\|_2^2r^{d+2}+O(\|u\|_2^2r^{d+1}).$$</div>
<p>For the second comparison, the quadratic weight changes by $O(\|u\|_2^2r)$ on each cube inside a ball of radius $r+O(1)$. Boundary cubes occupy a shell of volume $O(r^{d-1})$ and have weight $O(\|u\|_2^2r^2)$. The integral over the ball is the displayed leading term, by reflection and coordinate-permutation symmetry and radial integration.</p>
<p>Let $H=2a\chi_rS_2+D\chi_r^2$. For large radii $D&gt;0$, and <a href="/tag/6DOC/">6DOC</a> gives $S_2'=(1-e)H$ with $0\leq e=O(r^{3\alpha-d})$. Put $\eta=\min\{1,\varepsilon,d-3\alpha\}&gt;0$. The susceptibility hypothesis and lattice sums yield</p>
<div class="math-display">$$2(1-e)a\chi_r=\frac{2\alpha}r+O(r^{-1-\eta}),\qquad (1-e)D\chi_r^2\sim c_u r^{\alpha+1}.$$</div>
<p>The coefficient error is integrable, the forcing is nonnegative, and <a href="/tag/GAF9/">GAF9</a> now gives all three regimes. In the homogeneous-dominated case $\alpha&gt;2$, the positive constant retains the earlier-radius data; it is not fixed by the leading susceptibility coefficient.</p>
<p>This closes the analytic passage from a quantitative susceptibility estimate to the spatial scales for this specific kernel normalization. The factor $v_d$ is retained throughout. These second-moment equivalents do not establish tightness or identify a spatial scaling limit.</p>

## The displacement kernel of a cutoff model {#section-displacement-kernel}

<a id="tag-MWZ7" data-assertion="proposition" data-title="The bounded-jump displacement resolvent has exponential moments and a density"></a>
<p>Fix $d\geq1$, $0&lt;\alpha&lt;2$ and $c&gt;0$. On $\mathbb R^d\setminus\{0\}$, with Euclidean norm, define the symmetric Lévy measure</p>
<div class="math-display">$$\Pi(dx)=c\mathbf1_{\{0&lt;|x|&lt;1\}}\left(\int_{|x|}^1s^{-d-\alpha-1}\,ds\right)dx.$$</div>
<p>Let $L$ be the centered pure-jump Lévy process with this measure and no Gaussian part, and let $T$ be an independent exponential time of rate one. Then the law of $L_T$ has an even probability density $\kappa$, and $\int e^{\varepsilon|x|}\kappa(x)\,dx&lt;\infty$ for some $\varepsilon&gt;0$. For $u$ near zero,</p>
<div class="math-display">$$\mathbb E e^{\langle u,L_T\rangle}=\frac1{1-\Psi(u)},\qquad \Psi(u)=\int(\cosh\langle u,x\rangle-1)\Pi(dx)=c\sum_{m\geq1}\frac{\int_{B_1}\langle u,y\rangle^{2m}\,dy}{(2m)!(2m-\alpha)}.$$</div>
<p>For every $q&gt;0$, $\int|x|^q\Pi(dx)$ is finite exactly when $q&gt;\alpha$. In particular, the first absolute moment of the Lévy measure is infinite when $1\leq\alpha&lt;2$, although $L_T$ has all absolute moments.</p>
<p><em>Proof.</em> Near zero the density of $\Pi$ is comparable to $|x|^{-d-\alpha}$. Radial integration gives the asserted moment criterion and, since $\alpha&lt;2$, the Lévy integrability condition. On the bounded support, $\cosh\langle u,x\rangle-1$ is bounded by a constant depending on $u$ times $|x|^2$. Thus $\Psi(u)$ is finite for every $u$, continuous at zero and zero there. The Lévy exponential formula gives $\mathbb E e^{\langle u,L_t\rangle}=e^{t\Psi(u)}$. Integration against $e^{-t}dt$ gives the displayed resolvent when $\Psi(u)&lt;1$. Tonelli, followed by the substitution $x=sy$, gives its series. Taking the finitely many vectors $u=\pm\varepsilon\sqrt d\,e_j$ proves the exponential absolute-moment bound, since $e^{\varepsilon|x|}\leq\sum_j(e^{\varepsilon\sqrt d x_j}+e^{-\varepsilon\sqrt d x_j})$.</p>
<p>For the density, write $\psi(\xi)=\int(1-\cos\langle\xi,x\rangle)\Pi(dx)$. If $|\xi|$ is large, restrict the integral to $|x|\leq1/(2|\xi|)$. On this ball, $1-\cos\langle\xi,x\rangle\geq c_0\langle\xi,x\rangle^2$ and the Lévy density is bounded below by a positive multiple of $|x|^{-d-\alpha}$. Angular integration therefore gives $\psi(\xi)\geq c_1|\xi|^\alpha$. For each $t&gt;0$, the characteristic function $e^{-t\psi(\xi)}$ is integrable, so Fourier inversion supplies a density of $L_t$. Mixing these densities against $e^{-t}dt$ gives an integrable probability density for $L_T$. No finite-first-moment assumption on $\Pi$ is used.</p>
<p>This kernel retains both the cutoff in the jumps and the exponential killing. An untruncated symmetric nondegenerate $\alpha$-stable process stopped at $T$ instead has characteristic function $(1+a|\xi|^\alpha)^{-1}$ for some $a&gt;0$, and has infinite second moment when $\alpha&lt;2$. Indeed, for a nonzero one-dimensional projection the quotient $(1-\operatorname{Re}\mathbb E e^{ihX})/h^2$ diverges as $h\to0$; finite second moment would give a finite limit by dominated convergence. The unkilled potential measure $\int_0^\infty\mathbb P(L_t\in\cdot)dt$ has infinite total mass, by Tonelli. Neither object can replace the probability density $\kappa$ above in the cutoff diagram formula.</p>
<p>In <a href="https://arxiv.org/html/2508.18807v1">Critical LRP I</a>, (I.5.16) and Definition I.5.16 specify the corresponding bounded-jump measure and exponentially stopped displacement law, with the paper's norm and normalization. For $\alpha\geq2$, the displacement kernel is instead the density of Brownian motion at an independent rate-one exponential time; its moment generating function is $(1-\tfrac12u^\mathsf T\Sigma u)^{-1}$ near zero. Removing the cutoff is a separate step in §I.5.4. The notes' description of the cutoff kernel as stable must be read with this distinction; see the <a href="/errata/notes/#cutoff-displacement-kernel">provisional erratum</a>.</p>

## Probability kernels on the reduced tree {#section-tree-moments}

<a id="tag-GFEM" data-assertion="proposition" data-title="Normalized tree integrals are joint moments of independent edge displacements"></a>
<p>Let $\kappa$ be an even probability density on $\mathbb R^d$ with $\int e^{\varepsilon|x|}\kappa(x)dx&lt;\infty$ for some $\varepsilon&gt;0$. For $n\geq1$, let $\mathbb T_n$ be the trivalent trees with leaves labelled $0,1,\ldots,n$, as in <a href="/tag/SO5J/">the tree-shape count</a>. Fix the position of leaf $0$ at zero. For polynomials $P_1,\ldots,P_n$, define</p>
<div class="math-display">$$D_n(P_1,\ldots,P_n)=\sum_{T\in\mathbb T_n}\int_{(\mathbb R^d)^{2n-1}}\left[\prod_{\{v,w\}\in E(T)}\kappa(x_v-x_w)\right]\prod_{i=1}^nP_i(x_i)\prod_{v\ne0}dx_v.$$</div>
<p>All these integrals are absolutely convergent. Each tree integral is the expectation of $\prod_iP_i(X_i)$ when independent increments of density $\kappa$ are assigned to its edges, directed away from leaf $0$, and $X_i$ is the sum along the path to leaf $i$. Consequently</p>
<div class="math-display">$$D_n(1,\ldots,1)=(2n-3)!!.$$</div>
<p>The sum of the resulting leaf-position probability measures has a finite exponential moment of $\sum_i|X_i|$ in a neighbourhood of zero.</p>
<p><em>Proof.</em> Orient the tree away from $0$ and set $z_v=x_v-x_{\operatorname{parent}(v)}$. Ordering vertices by distance from the root makes this a triangular linear change of variables with determinant one. The density becomes $\prod_{v\ne0}\kappa(z_v)$; evenness removes any choice of orientation in the original product. Each $X_i$ is a finite sum of increments, and $\sum_i|X_i|\leq n\sum_{v\ne0}|z_v|$. Independence and the exponential-moment hypothesis give an exponential moment for the leaf vector at every sufficiently small positive parameter. This dominates every polynomial and proves absolute integrability. With all polynomials equal to one, each tree contributes one; there are $(2n-3)!!$ shapes, including one edge for $n=1$.</p>
<p>The normalization is substantive: the lines of the cutoff diagram carry a probability resolvent. The unit integral of each tree is what recovers the scalar double-factorial volume moments. Pointwise asymptotics for multipoint connection probabilities do not follow just from these integrated identities.</p>

## Changing from cutoff radius to spatial radius {#section-physical-normalization}

<a id="tag-57FJ" data-assertion="proposition" data-title="Spatial normalization changes the regular-variation indices"></a>
<p>Let $\alpha&gt;0$, $\gamma=\max\{1,\alpha/2\}$ and $\beta=\alpha/\gamma=\min\{\alpha,2\}$. Suppose positive measurable functions $\chi(r)$ and $\widehat m(r)$ are regularly varying at infinity with indices $\alpha$ and $2\alpha$, respectively. Let $q(R)$ be regularly varying with index $1/\gamma$ and define</p>
<div class="math-display">$$\eta(R)=\frac{4\chi(q(R))}{\widehat m(q(R))},\qquad\zeta(R)=\frac{\widehat m(q(R))}{4}.$$</div>
<p>Then $\eta$ and $\zeta$ are regularly varying with indices $-\beta$ and $2\beta$, and $\eta(R)\zeta(R)=\chi(q(R))$. In particular, their indices are $-2$ and $4$ when $\alpha&gt;2$.</p>
<p><em>Proof.</em> For each $s&gt;0$, $q(sR)/q(R)\to s^{1/\gamma}$. The uniform convergence theorem for measurable regularly varying functions on compact multiplier intervals gives</p>
<div class="math-display">$$\frac{\chi(q(sR))}{\chi(q(R))}\longrightarrow s^{\alpha/\gamma},\qquad\frac{\widehat m(q(sR))}{\widehat m(q(R))}\longrightarrow s^{2\alpha/\gamma}.$$</div>
<p>Take their quotient for $\eta$ and use the second ratio for $\zeta$. Their product identity follows directly from the definitions.</p>
<p>In the spatial theory, $q$ is an inverse, or an asymptotic inverse, of the spatial scale $\sigma(r)$. An eventually increasing scale of positive index $\gamma$ has an asymptotic inverse of index $1/\gamma$. Thus $\sigma(r)\sim c r^{\alpha/2}$ in the short-range case changes the powers when the variable is the spatial radius $R$. At $\alpha=2$, logarithmic factors affect the slowly varying parts but not these indices. The <a href="/errata/hutchcroft-lrp-1/#spatial-normalization-indices">provisional source erratum</a> records the distinction; no previously tagged normalization is changed.</p>

## Compactly supported moments of the canonical measure {#section-green-moments}

<a id="tag-5VYE" data-assertion="proposition" data-title="A Green-kernel tree bound gives factorial compact-test moments"></a>
<p>Let $0&lt;\beta&lt;d/2$ and let $G$ be a nonnegative symmetric measurable kernel on $\mathbb R^d$ satisfying $G(x)\leq A|x|^{\beta-d}$ for almost every $x\ne0$. For $n\geq1$, let $\mathbb T_n$ consist of the unrooted binary trees with leaves labelled $0,\ldots,n$, and fix the position of leaf $0$ at zero. Suppose a positive measure $\mathcal N$ on finite nonnegative Borel measures satisfies, for every nonnegative compactly supported continuous $\varphi$,</p>
<div class="math-display">$$\mathcal N[\mu[\varphi]^n]=4^{n-1}\sum_{T\in\mathbb T_n}\int\prod_{\{u,v\}\in E(T)}G(x_u-x_v)\prod_{i=1}^n\varphi(x_i)\prod_{v\ne0}dx_v.$$</div>
<p>Then for every real compactly supported continuous $\varphi$ there is a finite $C_\varphi$ such that</p>
<div class="math-display">$$\mathcal N[|\mu[\varphi]|^n]\leq C_\varphi^n n!\qquad(n\geq1).$$</div>
<p><em>Proof.</em> Write $H(x)=|x|^{\beta-d}$. Choose a ball $B$ about zero containing the support of $\varphi$ and a continuous function $\psi$ equal to one on that support, with $0\leq\psi\leq\mathbf1_B$. Put $h=H*\mathbf1_B$. Local integrability of $H$ and comparison outside twice the radius of $B$ give</p>
<div class="math-display">$$h(x)\asymp_B(1+|x|)^{\beta-d},\qquad \int h(x)^2\,dx&lt;\infty.$$</div>
<p>The latter uses exactly $d&gt;2\beta$. We claim that $H*h^2\leq C_Bh$. For bounded $x$, the convolution is bounded: its singularity is locally integrable, and its tail is integrable since $3\beta&lt;2d$. For $R=|x|$ large, split the convolution integral into $|y|\leq R/2$, $|x-y|\leq R/2$, and the region where both distances exceed $R/2$. The three contributions are bounded, respectively, by</p>
<div class="math-display">$$CR^{\beta-d}\int h^2,\qquad CR^{2\beta-2d}\int_{|w|\leq R/2}|w|^{\beta-d}\,dw\leq CR^{3\beta-2d},\qquad CR^{3\beta-2d}.$$</div>
<p>For the last bound, rescale by $R$: both possible singularities have been removed and the remaining integral converges at infinity because $3\beta&lt;2d$. Since $2\beta&lt;d$, both latter bounds are $O(R^{\beta-d})$, proving the claim.</p>
<p>Orient a fixed tree away from leaf $0$ and integrate from its marked leaves inward. Replacing $G$ by $AH$ only enlarges the nonnegative integral. For the kernel $H$, a terminal edge contributes at most $h$; a branch joins two such contributions by the operation $(f_1,f_2)\mapsto H*(f_1f_2)$. Induction over the $n-1$ branch vertices bounds the diagram with leaf factors $\mathbf1_B$ by $C_B^{n-1}h(0)$. There are $2n-1$ edges, so restoring the factors $A$ gives at most $A^{2n-1}C_B^{n-1}h(0)$ per tree.</p>
<p>There are $(2n-3)!!$ tree shapes, with the value one when $n=1$, by <a href="/tag/SO5J/">SO5J</a>. Since $(2n-3)!!\leq2^{n-1}(n-1)!$, summing the diagrams and including the factor $4^{n-1}$ proves an exponential-in-$n$ constant times $n!$ for $\mu[\psi]^n$. Finally $|\mu[\varphi]|\leq\|\varphi\|_\infty\mu[\psi]$, which proves the assertion.</p>
<p>This supplies the continuum tree estimate used in <a href="https://arxiv.org/html/2508.18807v1">Critical LRP I</a>, Lemma I.5.34. The kernel bound and canonical moment formula (I.1.11) are explicit inputs. For the intended Brownian or stable motions, $\beta=\min\{2,\alpha\}$; their Green-kernel estimates must be supplied when applying the proposition. The estimate controls compact spatial tests. It is not a finite-total-mass moment bound for $\mathcal N$, which is not a probability law.</p>

## From a probability resolvent to the Green kernel {#section-kernel-rescaling}

<a id="tag-42PB" data-assertion="proposition" data-title="Rescaled cutoff resolvents converge to the full Green kernel and its tree diagrams"></a>
<p>Consider either Brownian motion with positive definite covariance matrix in dimension $d&gt;2$, or the following normalized isotropic jump process with $0&lt;\alpha&lt;2$ and $d&gt;\alpha$. Write $v_d$ for the Euclidean unit-ball volume and set</p>
<div class="math-display">$$\Pi_r(dx)=\frac{\alpha}{v_d}\mathbf1_{\{0&lt;|x|&lt;r\}}\left(\int_{|x|}^r u^{-d-\alpha-1}\,du\right)dx\qquad(0&lt;r\leq\infty).$$</div>
<p>Let $\kappa$ be the density at an independent rate-one exponential time, using Brownian motion in the first case and the symmetric process with Lévy measure $\Pi_1$ in the second. Put $\beta=2$ in the Brownian case and $\beta=\alpha$ in the jump case. If $G$ is the Green kernel of the Brownian motion or the full $\Pi_\infty$ process, respectively, then</p>
<div class="math-display">$$K_s(x):=s^{\beta-d}\kappa(x/s)\leq G(x),\qquad K_s\longrightarrow G\text{ in }L^1_{\rm loc}(\mathbb R^d)\quad(s\to\infty).$$</div>
<p>The inequality is understood almost everywhere. Moreover, if $d&gt;2\beta$, every fixed binary-tree integral with compactly supported bounded leaf factors converges when all its edge kernels $K_s$ are replaced in the limit by $G$.</p>
<p><em>Proof.</em> For Brownian motion, scaling gives $K_s(x)=\int_0^\infty e^{-t/s^2}p_t(0,x)\,dt$. The integrand increases to that of $G$ as $s$ increases, and $G$ is locally integrable when $d&gt;2$. Monotone convergence on compact sets proves both claims about the kernel.</p>
<p>For the jump process, denote its time-$t$ density with cutoff $r$ by $p_t^r$. Scaling its Lévy measure gives $sL_t^1\stackrel{\rm law}=L_{s^\alpha t}^s$, so</p>
<div class="math-display">$$K_s(x)=\int_0^\infty e^{-s^{-\alpha}t}p_t^s(0,x)\,dt.$$</div>
<p>The difference of Lévy measures is a positive finite measure, even though each measure has infinite mass near zero. Tonelli gives its total mass:</p>
<div class="math-display">$$(\Pi_\infty-\Pi_s)(\mathbb R^d)=\frac{\alpha}{v_d}\int_s^\infty u^{-d-\alpha-1}|B_u|\,du=s^{-\alpha}.$$</div>
<p>Consequently the full process can be obtained by adding an independent compound Poisson process of this rate. On the event of no added jump by time $t$, its position equals that of the cutoff process. Thus $p_t^\infty\geq e^{-s^{-\alpha}t}p_t^s$, and the difference of these densities has integral $1-e^{-s^{-\alpha}t}$. In particular, $K_s\leq G$.</p>
<p>The full characteristic exponent is a positive constant times $|\xi|^\alpha$. Fourier inversion bounds $p_t^\infty$ by $Ct^{-d/\alpha}$, so the Green kernel is locally integrable: integrate probabilities over $0&lt;t\leq1$ and use this bound for $t\geq1$. For a compact set $B$ and $T&gt;0$,</p>
<div class="math-display">$$\int_B(G-K_s)\leq\int_0^T(1-e^{-s^{-\alpha}t})\,dt+\int_T^\infty\int_Bp_t^\infty(0,x)\,dx\,dt.$$</div>
<p>First let $s$ increase, then $T$. The first term tends to zero and the second has an integrable time tail, proving local $L^1$ convergence. Rotation and stable scaling give $G(x)=c|x|^{\alpha-d}$ almost everywhere, with a finite positive $c$. For Brownian motion the corresponding formula uses the covariance ellipsoid, and in particular $G(x)\leq C|x|^{2-d}$.</p>
<p>For the tree assertion, <a href="/tag/5VYE/">5VYE</a> makes the product of Green kernels times the absolute leaf factors integrable. From any sequence $s\to\infty$, local $L^1$ convergence gives a subsequence converging almost everywhere on all of space. The same holds after each edge-difference substitution: the inverse image of a null set under that surjective linear map is null. There are finitely many edges. Dominated convergence therefore applies to their product. Every sequence has such a subsequence with the same limiting integral, which proves convergence without assuming pointwise convergence of the original kernel family.</p>
<p>This proves the kernel passage behind Lemmas I.5.35–I.5.36 of <a href="https://arxiv.org/html/2508.18807v1">Critical LRP I</a> for the stated isotropic normalization and for nondegenerate Brownian motion. The equality of the omitted jump rate and the rescaled killing rate supplies the domination. An application with a different norm or normalization must check those constants and its Green-kernel bound.</p>

## Spatial tightness after removing the cutoff {#section-full-spatial-tightness}

<a id="tag-ALO4" data-assertion="proposition" data-title="Cutoff second moments and negligible added mass prevent spatial escape"></a>
<p>Let $\mu_R,\nu_{R,s}$ and $\eta_R$ satisfy $\nu_{R,s}\leq\mu_R$ and the discrepancy assumption in <a href="/tag/BB3O/">BB3O</a>. Suppose that for every fixed $s\geq1$,</p>
<div class="math-display">$$A_s:=\limsup_{R\to\infty}\eta_R^{-1}\mathbb E\int|x|^2\,d\nu_{R,s}(x)&lt;\infty.$$</div>
<p>Then for every $\varepsilon&gt;0$,</p>
<div class="math-display">$$\lim_{L\to\infty}\limsup_{R\to\infty}\eta_R^{-1}\mathbb P\bigl(\mu_R(\{|x|&gt;L\})&gt;\varepsilon\bigr)=0.$$</div>
<p>The same bound holds uniformly over all $s\geq1$ with $\nu_{R,s}$ in place of $\mu_R$.</p>
<p><em>Proof.</em> Fix an auxiliary cutoff $t$. If the full measure has more than $\varepsilon$ mass outside $B_L$, either $m(\mu_R-\nu_{R,t})&gt;\varepsilon/2$ or $\int|x|^2d\nu_{R,t}&gt;\varepsilon L^2/2$. Hence</p>
<div class="math-display">$$\limsup_{R\to\infty}\frac{\mathbb P(\mu_R(B_L^c)&gt;\varepsilon)}{\eta_R}
\leq\limsup_{R\to\infty}\frac{\mathbb P(m(\mu_R-\nu_{R,t})&gt;\varepsilon/2)}{\eta_R}+\frac{2A_t}{\varepsilon L^2}.$$</div>
<p>Choose $t$ to make the first term small, then $L$ to make the second small. Domination by $\mu_R$ gives the uniform cutoff assertion. No bound on $A_t$ uniform in $t$ is needed.</p>
<p>For a cutoff cluster embedded at spatial scale $R$ and mass scale $z_R$, the expectation here is $\chi_r\xi_2(r)^2/(z_RR^2)$, where $r=q(sR)$. Thus the usual cutoff susceptibility and radius-of-gyration asymptotics give a finite $A_s$ for each fixed $s$. This is the tightness step of Lemma I.5.32; a full-model second spatial moment is unnecessary.</p>

## Absolute bounds for mixed spatial moments {#section-mixed-moment-bounds}

<a id="tag-VMEJ" data-assertion="proposition" data-title="Volume bias bounds absolute mixed spatial moments by one-point moments"></a>
<p>Let $K$ be a random finite nonempty subset of $\mathbb R^d$ with $\chi=\mathbb E|K|&lt;\infty$. Under the probability law $Q$ obtained by weighting by $|K|/\chi$, choose $X$ uniformly from $K$. Let $P_1,\ldots,P_n$ be products of linear forms $\langle x,u\rangle$, with total degree $p\geq1$. Then</p>
<div class="math-display">$$\mathbb E\left[\sum_{x_1,\ldots,x_n\in K}\prod_{i=1}^n|P_i(x_i)|\right]
\leq\chi\left(\mathbb E_Q|K|^{2n-2}\right)^{1/2}\max_u\left(\mathbb E_Q|\langle X,u\rangle|^{2p}\right)^{1/2},$$</div>
<p>where the maximum is over the finitely many linear factors used in the monomials. Expectations may be infinite. If the directions are unit vectors and, for fixed $n,p$,</p>
<div class="math-display">$$\mathbb E_Q|K|^{2n-2}\leq(1+o(1))(4n-5)!!\,m^{2n-2},\qquad
\max_u\mathbb E_Q|\langle X,u\rangle|^{2p}\leq(1+o(1))C_0^{2p}(2p)!\,\sigma^{2p},$$</div>
<p>then the mixed moment is at most $(1+o(1))C^{n+p}n!p!\,\chi m^{n-1}\sigma^p$, with $C$ independent of $n,p$. The error is taken at each fixed pair; it is not asserted uniformly as the degrees grow.</p>
<p><em>Proof.</em> Conditional on $K$, sample $n$ independent uniform points. Apply Hölder with exponent $p$ to the $p$ individual absolute linear factors, then the arithmetic-geometric mean inequality. The conditional average of their product is at most the average, over those factors, of $|K|^{-1}\sum_{x\in K}|\langle x,u\rangle|^p$. Multiplying by $|K|^n$ and taking expectation gives at most</p>
<div class="math-display">$$\chi\max_u\mathbb E_Q\left[|K|^{n-1}|\langle X,u\rangle|^p\right].$$</div>
<p>Cauchy–Schwarz proves the first inequality without any independence between $X$ and $|K|$. For the second, $\sqrt{(2p)!}\leq2^pp!$ and $\sqrt{(4n-5)!!}\leq4^{n-1}(n-1)!$; the latter follows by bounding the middle binomial coefficient in $(4n-4)!/[2^{2n-2}(2n-2)!]$. The convention for $n=1$ is $(-1)!!=1$. Absorb the numerical factors into $C$.</p>
<p>The zero-degree case is simply $\mathbb E|K|^n=\chi\mathbb E_Q|K|^{n-1}$. This proves the estimate underlying Lemma I.5.27 of Critical LRP I. It reduces an absolute mixed-moment bound to volume and one-point displacement bounds; it does not identify mixed-moment asymptotics.</p>

## Differentiating a mixed cluster moment {#section-mixed-russo}

<a id="tag-1K61" data-assertion="theorem" data-title="Exact mixed-moment derivative keeps the two clusters distinct"></a>
<p>Consider independent bonds on $\mathbb Z^d$ with probabilities $1-e^{-k_t(y-x)}$, where the off-diagonal intensities are symmetric, nondecreasing and locally absolutely continuous in $t$. Let $P_1,\ldots,P_n$ be real polynomials with total degree at most $p$, and put</p>
<div class="math-display">$$F(A)=\prod_{i=1}^n\sum_{z\in A}P_i(z),\qquad M(t)=\mathbb E_t F(K_0).$$</div>
<p>On every compact parameter interval $[a,b]$, assume $\dot k_t(y)\leq w(y)$ almost everywhere, where</p>
<div class="math-display">$$\sum_{y\ne0}w(y)(1+|y|^p)&lt;\infty,\qquad
\sum_z(1+|z|^p)\mathbb P_b(0\leftrightarrow z)&lt;\infty.$$</div>
<p>Then $M$ is locally absolutely continuous and, almost everywhere,</p>
<div class="math-display">$$M'(t)=\mathbb E_t\left[\sum_{x\in K_0}\sum_{y\notin K_0}\dot k_t(y-x)
\sum_{\varnothing\ne I\subseteq\{1,\ldots,n\}}
\left(\prod_{i\notin I}\sum_{z\in K_0}P_i(z)\right)
\left(\prod_{i\in I}\sum_{z\in K_y}P_i(z)\right)\right].$$</div>
<p>All displayed sums are absolutely integrable. Empty products equal one. The vertices assigned to $I$ belong to $K_y$, while the remaining vertices belong to $K_0$.</p>
<p><em>Proof.</em> On a finite vertex set, differentiate the product Bernoulli law. An edge with endpoints already connected has no effect. Otherwise, if one endpoint $x$ belongs to the root cluster and the other endpoint $y$ does not, opening the edge replaces $K_0$ by the disjoint union $K_0\cup K_y$. Expanding $F(K_0\cup K_y)-F(K_0)$ gives exactly the sum over nonempty $I$.</p>
<p>The derivative of the edge probability is $\dot k_t(y-x)e^{-k_t(y-x)}$. Multiplying the edge-forced-closed expectation by $e^{-k_t(y-x)}$ turns it into the ordinary expectation on the event that the two endpoint clusters are distinct. Each relevant unordered edge has exactly one orientation with $x\in K_0$, so no factor of two appears. This proves the finite-volume identity, including for signed polynomials.</p>
<p>To pass to the countable model, replace every polynomial by an absolute polynomial growth bound. For each assignment $I$, the marked connections in the two distinct clusters have disjoint witnesses. BK bounds their joint probability by the product of their multipoint connection probabilities. Apply the tree-graph bound to each factor and use edge displacements as coordinates. Every spatial monomial is bounded by a constant times one plus the sum of the $p$th powers of these displacements and of the joining displacement: for nonnegative $a_j$, $\prod_j a_j^{p_j}\leq(\sum_j a_j)^p$ when $\sum p_j\leq p$, after adding one. Thus each resulting diagram is summable using the assumed weighted two-point sum and weighted row sum. The bound at parameter $b$ and the envelope $w$ dominate all finite volumes and parameters in $[a,b]$.</p>
<p>Finite susceptibility makes every relevant full cluster finite almost surely. Under exhaustion, the cluster terms and the distinct-cluster indicator converge; any connection that exists has a finite witness. Dominated convergence therefore applies to both the derivative sums and their parameter integrals. The same tree bound controls $F(K_0)$ itself. Integrating the finite identity before passing to the limit proves the asserted integral identity and hence local absolute continuity and the a.e. derivative.</p>
<p>For monomials, expand each moved factor using $z=x+(y-x)+(z-y)$. Assigning its individual linear factors to these three summands gives the split functions $A_i(x)B_i(z-y)C_i(y-x)$. The source's Lemma I.5.28 is this calculation, but the inspected HTML display places all marked vertices in $K_0$; its following display (I.5.35) restores the $K_y$ summation for $i\in I$. The <a href="/errata/hutchcroft-lrp-1/#mixed-moment-cluster-index">provisional erratum</a> records that distinction. Factorization of the two dependent cluster terms is a further estimate, not part of Russo's identity.</p>

## The edge-insertion recurrence for spatial diagrams {#section-diagram-recurrence}

<a id="tag-IX97" data-assertion="theorem" data-title="A resolvent identity determines the split recurrence for tree moments"></a>
<p>Use either of the following even probability densities $\kappa$: nondegenerate Brownian motion stopped at an independent rate-one exponential time, or the similarly stopped symmetric Lévy process with measure</p>
<div class="math-display">$$\Pi(dx)=\frac{\alpha}{v}\mathbf1_{\{0&lt;\|x\|&lt;1\}}\left(\int_{\|x\|}^1t^{-d-\alpha-1}\,dt\right)dx,\qquad 0&lt;\alpha&lt;2,$$</div>
<p>where $\|\cdot\|$ is any norm, $B$ its unit ball and $v$ its Lebesgue volume. In the Brownian case put $\beta=2$ and $U=0$. In the jump case put $\beta=\alpha$ and let $U$ be uniform on $B$. These choices fix both the normalization and the law of $U$.</p>
<p>On a tree rooted at a vertex fixed at zero, put independent $\kappa$-distributed displacements on its $k$ edges, and let $X_v$ be the resulting vertex positions. If $P_v$ are homogeneous polynomials of total degree $p$, set $I=\mathbb E\prod_{v\ne0}P_v(X_v)$. For each edge $e$, let $I_e$ denote the same expectation with that edge displacement replaced by the sum of two independent $\kappa$ displacements and an independent copy of $U$. Then</p>
<div class="math-display">$$(p+\beta k)I=\beta\sum_e I_e.$$</div>
<p>In particular, let $D_n$ be the binary-tree diagram sum in GFEM. Write each monomial $P_i$ as a product of individually labelled linear factors. A split $S$ consists of a nonempty subset $I\subseteq\{1,\ldots,n\}$ and, for every $i\in I$, an assignment of its factors to three groups, with products $A_i,B_i,C_i$. Count assignments separately even when repeated factors give the same products. Put</p>
<div class="math-display">$$P^-_S=\left((P_i)_{i\notin I},\prod_{i\in I}A_i\right),\qquad
P^+_S=(B_i)_{i\in I},\qquad c_S=\mathbb E\prod_{i\in I}C_i(U).$$</div>
<p>For $n\geq2$ and total degree $p\geq1$, remove the split with $I=\{1,\ldots,n\}$ and every factor assigned to $B$, and the $n$ splits with $I=\{j\}$ and every factor assigned to $A$. Denote the remaining assignments by $\mathscr S'$. Then</p>
<div class="math-display">$$(p+\beta(n-2))D_n(P_1,\ldots,P_n)
=\beta\sum_{S\in\mathscr S'}D_{n-|I|+1}(P^-_S)D_{|I|}(P^+_S)c_S.$$</div>
<p>Each factor on the right has either fewer marked vertices or the same number with smaller total degree. Together with the one-point moments and $D_n(1,\ldots,1)=(2n-3)!!$, this determines every monomial diagram.</p>
<p><em>Proof.</em> The bounded-jump argument in MWZ7 extends by norm equivalence: it gives a density and exponential moments near zero. Let $K(u)=\int e^{\langle u,x\rangle}\kappa(x)dx$ and write $B(u)=\mathbb E e^{\langle u,U\rangle}$. In the jump case, the Lévy cumulant and resolvent are</p>
<div class="math-display">$$\Psi(u)=\alpha\int_0^1 t^{-\alpha-1}(B(tu)-1)\,dt,\qquad K(u)=\frac1{1-\Psi(u)}.$$</div>
<p>Integrating by parts in the first formula yields $u\cdot\nabla\Psi=\alpha(B-1+\Psi)$; the boundary term at zero vanishes because $B(tu)-1=O(t^2)$ and $\alpha&lt;2$. Hence</p>
<div class="math-display">$$(u\cdot\nabla+\beta)K(u)=\beta B(u)K(u)^2.$$</div>
<p>For Brownian motion, $\Psi(u)=u^{\mathsf T}\Sigma u/2$ and $B(u)=1$, giving the same identity with $\beta=2$. All power series used here converge in a neighborhood of zero.</p>
<p>The generating function for the independent edge increments is $\prod_eK(u_e)$. Apply the sum of the Euler operators $u_e\cdot\nabla_{u_e}$ and add $\beta k$. Comparing the coefficients of any homogeneous polynomial of degree $p$ gives the first assertion: the factor $B(u_e)K(u_e)^2$ replaces just the $e$th displacement by the specified sum. The vertex polynomial is homogeneous of the same degree in edge coordinates, so this coefficient identity applies to $I$.</p>
<p>Now apply it to every binary tree, with polynomial $1$ at each internal vertex; there are $k=2n-1$ edges. Cutting the selected edge splits the diagram into a tree containing root $0$ and a second tree with a new root. Let $I$ be the set of marked leaves in the second part. The two inserted $\kappa$ edges terminate at the new cut leaves, whose displacement is $U$. A marked position in the second part is the sum of the first cut position, $U$, and its position relative to the second cut leaf. Expanding its labelled linear factors produces precisely $P^-_S$, $P^+_S$ and $c_S$.</p>
<p>This decomposition is a bijection between a tree with a selected edge and a pair of trees with their cut leaves distinguished; gluing and removing the two cut leaves recovers the original edge. There is therefore no extra counting factor. The $n+1$ excluded assignments each contribute $D_n(P_1,\ldots,P_n)$, since their other diagram is $D_1(1)=1$ and their $U$ factor is one. Move these terms to the left to obtain the stated coefficient. All other splits decrease the lexicographic pair (number of marked vertices, total degree), and the coefficient is positive for $n\geq2$, $p\geq1$.</p>
<p>This proves the diagram recurrence in Proposition I.5.30 and the last part of the proof of Theorem I.5.21 of Critical LRP I, using generating functions instead of differentiating transition densities. The uniform-ball law is essential in the jump case; in the Brownian case all assignments with a nonconstant $C_i$ vanish.</p>

## Closing a factorized mixed-moment hierarchy {#section-mixed-hierarchy}

<a id="tag-GY8M" data-assertion="theorem" data-title="A factorized spatial-moment equation has the binary-tree asymptotics"></a>
<p>Fix $\alpha&gt;0$ and the corresponding kernel of IX97: the jump kernel if $\alpha&lt;2$, and a nondegenerate Brownian kernel if $\alpha\geq2$. Let $\chi,m,\sigma$ be positive functions, regularly varying with indices $\alpha,2\alpha,\gamma$, where $\gamma=1$ for $\alpha&lt;2$ and $\gamma=\alpha/2$ otherwise. Assume $\sigma(r)=r$ in the first case and $r/\sigma(r)\to0$ in the second. For every list of monomials $P=(P_1,\ldots,P_n)$ of total degree $p$, suppose a locally absolutely continuous function $M_P$ is given, invariant under permutation of the list. Assume $M_{(1)}=\chi$ and the boundary limits</p>
<div class="math-display">$$\frac{M_{(P_1)}(r)}{\chi(r)\sigma(r)^p}\longrightarrow D_1(P_1),\qquad
\frac{M_{(1,\ldots,1)}(r)}{\chi(r)m(r)^{n-1}}\longrightarrow(2n-3)!!.$$</div>
<p>Set $H_{n,p}=\chi m^{n-1}\sigma^p$. Use the labelled splits of IX97, now writing $q(S)=\deg\prod_{i\in I}C_i$ and $b_S=v^{-1}\int_B\prod_{i\in I}C_i(y)dy$ for a fixed norm ball $B$ of volume $v$. Suppose, for each fixed list $P$, that $M_P=O(H_{n,p})$ and, almost everywhere,</p>
<div class="math-display">$$rM_P'(r)=\frac{\alpha}{\chi(r)}\sum_{S\in\mathscr S}b_S r^{q(S)}M_{P^-_S}(r)M_{P^+_S}(r)+o(H_{n,p}(r)).$$</div>
<p>For $\alpha&lt;2$, the ball here is the one defining the jump kernel. Then for every list of monomials,</p>
<div class="math-display">$$\frac{M_P(r)}{\chi(r)m(r)^{n-1}\sigma(r)^p}\longrightarrow D_n(P_1,\ldots,P_n).$$</div>
<p>If the family extends multilinearly to polynomial arguments, the equivalent statement for general polynomials is</p>
<div class="math-display">$$\frac{M_{(P_1(\cdot/\sigma(r)),\ldots,P_n(\cdot/\sigma(r)))}(r)}{\chi(r)m(r)^{n-1}}\longrightarrow D_n(P_1,\ldots,P_n).$$</div>
<p><em>Proof.</em> Induct lexicographically on $(n,p)$, with the asserted boundaries supplying $n=1$ and $p=0$. Let $n\geq2$, $p\geq1$. The $n+1$ exceptional splits of IX97 give exactly $(n+1)\alpha M_P$ on the right: each has $q=0$, $b_S=1$ and the second moment factor $M_{(1)}=\chi$.</p>
<p>For every remaining split the induction hypothesis applies to both factors, and their normalizations multiply to $\chi^2m^{n-1}\sigma^{p-q(S)}$. Thus</p>
<div class="math-display">$$rM_P'=(n+1)\alpha M_P+(A_P+o(1))H_{n,p},$$</div>
<p>where $A_P=\alpha\sum_{\mathscr S'}D(P^-_S)D(P^+_S)b_S$ if $\alpha&lt;2$. If $\alpha\geq2$, only terms with $q(S)=0$ remain in this sum: each other term contains the vanishing factor $(r/\sigma(r))^{q(S)}$. There are finitely many splits at fixed degree, so these limits can be taken term by term, including when a limiting factor is zero.</p>
<p>The index of $H_{n,p}$ is $(2n-1)\alpha+\gamma p$, whose difference from $(n+1)\alpha$ is $(n-2)\alpha+\gamma p&gt;0$. Apply <a href="/tag/2KB9/">2KB9</a>. In the jump case the resulting limit is</p>
<div class="math-display">$$\frac{\alpha}{p+(n-2)\alpha}\sum_{\mathscr S'}D(P^-_S)D(P^+_S)b_S=D_n(P),$$</div>
<p>by IX97. In the Brownian case the coefficient becomes $2/[p+2(n-2)]$, and the $q=0$ sum is exactly the Brownian recurrence. This proves the induction. Signed and odd-degree moments are included; no division by a possibly zero limiting moment was used. Expanding each rescaled polynomial into monomials, with its own degree-dependent power of $\sigma(r)$, gives the last assertion by a finite sum.</p>
<p>The bound $M_P=O(H_{n,p})$ records the absolute-moment control supplied by VMEJ in the percolation application. The signed ODE argument itself is stronger and does not require that bound. The factor $r^{q(S)}$ in the hypothesis comes from summing the joining-displacement polynomial over a ball of radius $r$; it cannot be omitted. See the <a href="/errata/hutchcroft-lrp-1/#mixed-moment-radius-factor">provisional erratum</a> for the displayed formula in Lemma I.5.29.</p>
<p>This closes the induction and identifies its constants once the factorized differential equation and boundary moments have been proved. In a percolation model, 1K61 supplies the exact two-cluster derivative; replacing it by the product expression above still requires a collision estimate with an error $o(H_{n,p}/r)$. The source proves that estimate separately in Lemma I.5.29 under its four alternatives. In particular, this theorem alone does not establish that estimate in the critical dimension.</p>

## Higher spatial moments and the collision error {#section-higher-spatial-error}

<a id="tag-QLN7" data-assertion="proposition" data-title="A weighted tree bound controls the single-point derivative error at every even degree"></a>
<p>For a translation-invariant independent bond model, let $\ell(x)=\langle x,u\rangle$, $\chi=\sum_x\tau(0,x)&lt;\infty$ and $S_q=\sum_x|\ell(x)|^q\tau(0,x)&lt;\infty$, where $q\geq1$. Then, for every integer $m\geq1$,</p>
<div class="math-display">$$\mathbb E\left[|K_0|^{m-1}\sum_{x\in K_0}|\ell(x)|^q\right]\leq(2m-3)!!(2m-1)^q\chi^{2m-2}S_q.$$</div>
<p>Now specialize to the Euclidean cutoff of 0CUF, assume finite cutoff susceptibility, and take an even integer $q\geq2$. Write $S_j(r)=\sum_x\ell(x)^j\tau_r(0,x)$, $S_0=\chi_r$, $c_r=br^{-d-\alpha-1}$ and $W_j(r)=\sum_{0&lt;|h|&lt;r}\ell(h)^j$. For almost every $r&gt;1$,</p>
<div class="math-display">$$0\leq c_r\sum_{a+b+c=q}\frac{q!}{a!b!c!}S_a(r)S_b(r)W_c(r)-S_q'(r)\leq3\cdot5^q c_r\chi_r^4S_q(r).$$</div>
<p><em>Proof.</em> Apply the tree-graph bound to the first expectation with $m$ marked vertices. On a tree with $E=2m-1$ edges, the marked displacement is the sum along a path of at most $E$ edges. Convexity gives $|\sum_{e\in P}\ell(h_e)|^q\leq |P|^{q-1}\sum_{e\in P}|\ell(h_e)|^q$. Summing in edge coordinates bounds each tree by $E^q\chi^{E-1}S_q$; sum over the $(2m-3)!!$ shapes. For $m=1$ this is the defining identity for $S_q$.</p>
<p>All required cutoff moments are finite: the path bound $|x|\leq r|K_0|$ and the volume tree bound suffice on every compact range of radii. Thus 1K61 applies to $P(z)=\ell(z)^q$. For fixed $x,y,z$, the difference between $\tau_r(0,x)\tau_r(y,z)$ and the two-cluster probability $\mathbb P_r(0\leftrightarrow x,\ y\leftrightarrow z,\ 0\not\leftrightarrow y)$ is nonnegative by BK and at most the probability that $0,x,y,z$ lie in one cluster, by Harris.</p>
<p>Multiply by $c_r\mathbf1_{\{0&lt;|y-x|&lt;r\}}\ell(z)^q$ and sum. The independent product term is the displayed multinomial expression after setting $h=y-x$ and translating $z$ by $y$. Dropping the window constraint in the error bounds it by $c_r\mathbb E[|K_0|^2\sum_{z\in K_0}\ell(z)^q]$. The first assertion with $m=3$ gives the claimed constant. Absolute integrability justifies both subtractions and changes of variables.</p>

## The one-point displacement moments in high dimension {#section-displacement-asymptotics}

<a id="tag-LDR1" data-assertion="theorem" data-title="All cutoff displacement moments converge to the normalized resolvent moments"></a>
<p>Assume the endpoint hypotheses and Euclidean kernel of 7F5O, with $d&gt;3\alpha$. Set $\sigma(r)=r$ when $\alpha&lt;2$, and otherwise set</p>
<div class="math-display">$$\sigma(r)^2=\frac1{\chi_r}\sum_x|x|^2\tau_r(0,x).$$</div>
<p>For $\alpha&lt;2$, let $\kappa$ be the jump resolvent in IX97 for the Euclidean unit ball. For $\alpha\geq2$, let it be the Brownian resolvent with covariance matrix $d^{-1}I$. Then for every polynomial $P$ on $\mathbb R^d$,</p>
<div class="math-display">$$\frac1{\chi_r}\sum_xP(x/\sigma(r))\tau_r(0,x)\longrightarrow\int P(z)\kappa(z)\,dz.$$</div>
<p><em>Proof.</em> Fix $u\ne0$ and write $S_j$ as in QLN7. Inversion symmetry gives $S_j=0$ for odd $j$. The case $j=0$ is normalization. For $j=2$ and $\alpha&lt;2$, Z11O and 7F5O give</p>
<div class="math-display">$$\frac{S_2(r)}{\chi_r r^2}\longrightarrow\frac{\alpha|u|^2}{(2-\alpha)(d+2)},$$</div>
<p>which is the second moment of the specified jump resolvent by its cumulant formula. For $\alpha\geq2$, coordinate reflections make the off-diagonal covariance terms zero and coordinate permutations make the diagonal terms equal. Consequently $S_2/(\chi_r\sigma^2)=|u|^2/d$ exactly, matching the Brownian covariance. Z11O also gives $\sigma\in\operatorname{RV}_{\alpha/2}$ and $r/\sigma(r)\to0$, including the logarithmic factor at $\alpha=2$.</p>
<p>Induct over the even degree $q\geq4$. Isolate the two terms $S_q\chi_r W_0$ in QLN7. Since $S_q&gt;0$ for $r&gt;1$, its derivative can be written</p>
<div class="math-display">$$S_q'=\left(2c_rW_0\chi_r-e_q(r)\right)S_q+F_q(r),\qquad0\leq e_q(r)\leq3\cdot5^q c_r\chi_r^4,$$</div>
<p>where $F_q$ is the remaining multinomial sum. The susceptibility estimate and lattice-ball asymptotics give $2c_rW_0\chi_r=2\alpha/r+O(r^{-1-\eta})$ for some $\eta&gt;0$, while $e_q=O(r^{-1+3\alpha-d})=o(1/r)$. The error is measurable and may be chosen arbitrarily on the null set where the derivative identity is not asserted.</p>
<p>For each integer $c\geq0$,</p>
<div class="math-display">$$W_c(r)=r^{d+c}\left(\int_{B_1}\ell(y)^c\,dy+o(1)\right),$$</div>
<p>by Riemann sums; odd terms vanish exactly. In every term of $F_q$, both spatial degrees $a,b$ are smaller than $q$. Write $\mu_j=\int\ell(z)^j\kappa(z)dz$. The induction hypothesis therefore gives, when $\alpha&lt;2$,</p>
<div class="math-display">$$\frac{rF_q(r)}{\chi_r\sigma(r)^q}\longrightarrow\alpha\sum_{\substack{a+b+c=q\\(a,b,c)\ne(q,0,0),(0,q,0)}}\frac{q!}{a!b!c!}\mu_a\mu_b\,\mathbb E\ell(U)^c.$$</div>
<p>When $\alpha\geq2$, only the terms with $c=0$ survive, because the others contain $(r/\sigma)^c$. Apply 2KB9 with $h=\chi_r\sigma^q$, whose index exceeds $2\alpha$ by $q-\alpha$ in the jump case and by $\alpha(q/2-1)$ in the Brownian case. The resulting limit is precisely $\mu_q$, by the one-edge identity in IX97 after its two self terms are removed. This completes the even-degree induction.</p>
<p>For each degree, powers of real linear forms span the homogeneous polynomials of that degree, as follows by polarization. The directional limits therefore give all homogeneous polynomial limits; a general polynomial is a finite sum of these with their respective powers of $\sigma$. The zero direction causes no exception.</p>
<p>The covariance $d^{-1}I$ is tied to the definition of $\sigma$ using the total Euclidean second moment. A different spatial normalization rescales the covariance. This proves the one-point input in the high-dimensional Euclidean regime, using the already proved susceptibility and second-moment estimates; it asserts no critical-dimensional extension.</p>

## Factorization of mixed moments above three alpha {#section-high-dimensional-factorization}

<a id="tag-2VIE" data-assertion="theorem" data-title="Mixed spatial derivatives factorize when the collision scale is negligible"></a>
<p>For the Euclidean cutoff of 0CUF, fix monomials $P_1,\ldots,P_n$ of total degree $p$. Suppose the cutoff clusters have finite moments of all required orders, and put $M_P(r)=\mathbb E_r\prod_i\sum_{z\in K_0}P_i(z)$. With $K,K'$ independent root clusters, define</p>
<div class="math-display">$$\mathcal F_P(r)=c_r\sum_{\varnothing\ne I\subseteq[n]}\mathbb E_r\left[\sum_{x\in K}\sum_{0&lt;|h|&lt;r}
\prod_{i\notin I}\sum_{z\in K}P_i(z)\prod_{i\in I}\sum_{z\in K'}P_i(x+h+z)\right],\qquad c_r=br^{-d-\alpha-1}.$$</div>
<p>For almost every $r$,</p>
<div class="math-display">$$|M_P'(r)-\mathcal F_P(r)|\leq(2^n-1)c_r\mathbb E_r\left[|K_0|^2\sum_{z_1,\ldots,z_n\in K_0}\prod_i|P_i(z_i)|\right].$$</div>
<p>Suppose, in addition, that $\chi_r\sim\alpha r^\alpha/(bv_d)$, $m_r=O(r^{2\alpha})$, $r/\sigma(r)=O(1)$, and the absolute mixed-moment bounds of VMEJ hold with scales $\chi_r,m_r,\sigma(r)$. If $d&gt;3\alpha$, then the factorized differential equation assumed in GY8M holds for $M_P$.</p>
<p><em>Proof.</em> Fix a nonempty assignment $I$, the joining endpoints $x,y$, and all marked vertices. Let $A$ be the event connecting the root, $x$, and the marked vertices outside $I$, and $B$ the event connecting $y$ to those inside $I$. The connection events in the exact derivative of 1K61 require these two clusters to be distinct. As in QLN7,</p>
<div class="math-display">$$0\leq\mathbb P(A)\mathbb P(B)-\mathbb P(A\cap B\cap\{0\not\leftrightarrow y\})\leq\mathbb P(0,x,y,z_1,\ldots,z_n\text{ lie in one cluster}).$$</div>
<p>Multiply by the absolute spatial weight and the joining-edge rate. Dropping the joining window permits the sums over $x,y$ to contribute $|K_0|^2$. There are $2^n-1$ assignments, which gives the first bound. This argument bounds the absolute error of signed moments; it does not assert that their derivative deficit has a sign.</p>
<p>VMEJ with two additional constant marked factors bounds the expectation by $C_P\chi_rm_r^{n+1}\sigma(r)^p$. Relative to $H_{n,p}/r=\chi_rm_r^{n-1}\sigma(r)^p/r$, the derivative error is therefore at most</p>
<div class="math-display">$$C_Pr^{-d-\alpha}m_r^2=O(r^{3\alpha-d})=o(1).$$</div>
<p>Expand each $P_i(x+h+z)$ by assigning its labelled linear factors to $x,h,z$. Independence makes the two cluster factors $M_{P^-_S}$ and $M_{P^+_S}$, while the joining sum has the asymptotic</p>
<div class="math-display">$$\sum_{0&lt;|h|&lt;r}\prod_{i\in I}C_i(h)=v_dr^{d+q(S)}(b_S+o(1)).$$</div>
<p>Thus $c_r$ times this sum equals $\alpha r^{q(S)-1}(b_S+o(1))/\chi_r$. The absolute moment bounds and boundedness of $r/\sigma$ show that every resulting Riemann-sum error is $o(H_{n,p}/r)$. There are finitely many assignments at each fixed degree. Summing them and adding the collision error gives exactly GY8M's equation, including its radius power.</p>
<p>The condition $d&gt;3\alpha$ is used where the collision ratio tends to zero. At equality this argument gives no vanishing error; the critical-dimensional estimate requires additional information and is not inferred here.</p>

## Mixed-moment and measure limits for the normalized model {#section-high-dimensional-mixed-limit}

<a id="tag-HBLN" data-assertion="theorem" data-title="The normalized high-dimensional cutoff model has the spatial tree-moment limit"></a>
<p>Assume the Euclidean kernel and endpoint hypotheses of 7F5O, with $d&gt;3\alpha$. Put $\chi_r=\mathbb E_r|K_0|$, $m_r=\mathbb E_r|K_0|^2/\chi_r$, and use $\sigma$ and $\kappa$ from LDR1. Then for every $n\geq1$ and real polynomials $P_1,\ldots,P_n$,</p>
<div class="math-display">$$\frac{1}{\chi_rm_r^{n-1}}\mathbb E_r\left[\sum_{x_1,\ldots,x_n\in K_0}\prod_{i=1}^nP_i(x_i/\sigma(r))\right]\longrightarrow D_n(P_1,\ldots,P_n).$$</div>
<p>Under bias by $|K_0|/\chi_r$, the random finite measure $m_r^{-1}\sum_{x\in K_0}\delta_{x/\sigma(r)}$ consequently converges weakly to the law determined by these diagrams in Y3SX; its total mass has the squared-standard-normal law.</p>
<p><em>Proof.</em> The susceptibility and scalar moment asymptotics are 7F5O and K3DB. They give $\chi\in\operatorname{RV}_\alpha$, $m\sim c r^{2\alpha}$ for a positive constant $c$, and the double-factorial boundary limits. LDR1 gives the one-point polynomial limits and the required spatial scale.</p>
<p>The resolvent has an exponential absolute moment, so its directional moments of degree $2p$ are bounded by $C^{2p}(2p)!$ uniformly over unit directions. LDR1 transfers these bounds asymptotically at each fixed degree and each finite list of directions. The size-biased volume moments follow from K3DB. VMEJ therefore supplies every required absolute mixed-moment bound, including with extra constant factors. The cutoff path estimate and scalar moments give all finite-radius integrability hypotheses in 1K61.</p>
<p>Apply 2VIE to obtain the factorized differential equation. All hypotheses of GY8M are now supplied, so its induction gives the displayed polynomial asymptotics. Y3SX then proves tightness and identifies the random-measure limit, without requiring an additional spatial mixed-moment input.</p>
<p>This proves the Euclidean $d&gt;3\alpha$ case of the cutoff spatial-moment argument from the stated endpoint assumptions. For $\alpha\geq2$ it imposes $d&gt;3\alpha$, rather than covering every effectively short-range case with $d&gt;6$. The general-norm alternatives and the critical-dimensional hydrodynamic argument remain separate. Identification of the limiting law with a named CRT occupation measure uses the geometric input in 45EB; the canonical measure without cutoff still uses its construction and moment formula in the subsequent cutoff-removal argument.</p>

## Source scope {#section-source}

<p>The soft cutoff is the fixed-normalization model of the notes, lines 4450–4488. The exact spatial derivative and upper bound supply part of the spatial-moment calculation in lines 5363–5545 (S035). The collision bound supplies the high-dimensional relative error and its logarithmic integrability under a separate susceptibility estimate. Precise coefficient asymptotics, critical-dimensional improvements, mixed-moment convergence and the superprocess identification remain separate. The final theorem is an analytic implication under explicit error hypotheses; it does not establish those errors for percolation or infer convergence of embedded clusters from volume moments.</p>

<p>The later HBLN theorem supplies the polynomial mixed-moment asymptotics and size-biased random-measure limit for the normalized Euclidean model with $d&gt;3\alpha$, under 7F5O’s endpoint hypotheses. Together with the full tail in 26NT, the omitted-edge bound C4E9 and the spatial scale Z11O, it supplies the percolation inputs to the cutoff-removal argument in the size-biased-laws article. Other model alternatives and the canonical superprocess construction remain separate.</p>

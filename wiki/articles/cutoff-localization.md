---
{
  "id": "cutoff-localization",
  "title": "Localization of cutoff clusters",
  "subtitle": "Spatial mass and volume moments",
  "kind": "method",
  "category": "Critical phenomena",
  "summary": "Correlation lengths control the mass outside a large ball. Localization of higher volume moments needs additional control of large clusters; a uniform moment-ratio bound supplies one sufficient condition.",
  "context": ["A countable metric vertex set with root $o$; $B_R=\\{x:d(o,x)\\leq R\\}$.", "For each real $r\\geq1$, $K_r$ is a random subset containing $o$, with measurable membership events and finite positive mean size.", "These are conditions on a family of laws. No coupling between different radii is assumed."],
  "related": ["spatial-cutoff-moments", "cutoff-families", "cutoff-scaling", "multipoint-trees"],
  "sourceIds": ["notes"],
  "aliases": ["CL", "wCL", "weak cutoff localization", "correlation-length condition", "radius of gyration"],
  "prototypeUses": []
}
---

## Spatial localization {#section-spatial}

<p>Write $X_r=|K_r|$, $m_q(r)=\mathbb E X_r^q$, and $\chi_r=m_1(r)$. In a cutoff percolation model, $K_r$ is the root cluster under the cutoff law at the full model's critical parameter. Finite susceptibility of that cutoff law is a hypothesis here.</p>

<a id="tag-J7SM" data-assertion="definition" data-title="Correlation-length condition"></a>
<p>For each finite real $p&gt;0$, define</p>
<div class="math-display">$$\xi_p(r)^p=\frac{1}{\chi_r}\mathbb E\sum_{x\in K_r}d(o,x)^p.$$</div>
<p>The family satisfies the correlation-length condition (CL) if, for every finite $p&gt;0$, there is a finite constant $C_p$ such that $\xi_p(r)\leq C_p r$ for every $r\geq1$. The constant may depend on $p$ but not on $r$.</p>
<p>The normalization weights a cluster by its mass and then samples a vertex uniformly from it. It is not the law obtained by first sampling an unweighted cluster and then a uniform vertex. The notes mention an infinity-radius convention separately; the quantified condition above concerns finite $p$.</p>

<a id="tag-32GP" data-assertion="proposition" data-title="A spatial moment localizes the first volume moment"></a>
<p>If $\xi_p(r)\leq C_p r$ for one fixed $p&gt;0$ and every $r\geq1$, then for every $C&gt;0$, writing $Z_{r,C}=|K_r\setminus B_{Cr}|$,</p>
<div class="math-display">$$\frac{\mathbb E Z_{r,C}}{\chi_r}\leq\left(\frac{C_p}{C}\right)^p.$$</div>
<p>Consequently, for each $\varepsilon&gt;0$ a single finite $C&gt;0$ gives $\chi_r\leq(1+\varepsilon)\mathbb E|K_r\cap B_{Cr}|$ for all $r\geq1$.</p>
<p><em>Proof.</em> Every vertex outside the ball contributes more than $(Cr)^p$ to the spatial sum. Take expectations and divide by $\chi_r(Cr)^p$. Since $X_r=|K_r\cap B_{Cr}|+Z_{r,C}$, it suffices to choose $C$ so that $(C_p/C)^p\leq\varepsilon/(1+\varepsilon)$.</p>
<p>This controls the expected mass lost outside the ball, rather than the probability that the entire cluster lies inside it. It also gives $\mathbb P(Z_{r,C}&gt;0)\leq\chi_r(C_p/C)^p$, but the latter bound need not be small uniformly when $\chi_r$ grows.</p>

## Localization of volume moments {#section-moments}

<a id="tag-AWWU" data-assertion="definition" data-title="Weak cutoff localization of four volume moments"></a>
<p>Suppose $m_q(r)&lt;\infty$ for $q=1,2,3,4$ and every $r\geq1$. The family satisfies weak cutoff localization (wCL) if for every $\varepsilon&gt;0$ there exists a finite $C&gt;0$ such that, simultaneously for $q=1,2,3,4$ and all $r\geq1$,</p>
<div class="math-display">$$m_q(r)\leq(1+\varepsilon)\mathbb E|K_r\cap B_{Cr}|^q.$$</div>
<p>The same ball radius factor must work for all four moments and all cutoff scales. The local count is the intersection of the full cutoff cluster with the ball, not the root cluster obtained by deleting paths that leave the ball.</p>

<a id="tag-39MV" data-assertion="theorem" data-title="Spatial localization and moment ratios imply weak cutoff localization"></a>
<p>Suppose the spatial bound $\xi_p(r)\leq C_p r$ holds for some fixed $p&gt;0$. Suppose also that the moments through order seven are finite and that, for each $q=2,3,4$, there is a finite constant $A_q$ such that</p>
<div class="math-display">$$\frac{m_{2q-1}(r)\chi_r}{m_q(r)^2}\leq A_q\qquad(r\geq1).$$</div>
<p>Then (wCL) holds. More precisely, with $A_1=1$ and $Y_{r,C}=|K_r\cap B_{Cr}|$,</p>
<div class="math-display">$$0\leq\frac{m_q(r)-\mathbb E Y_{r,C}^q}{m_q(r)}\leq q\sqrt{A_q}\left(\frac{C_p}{C}\right)^{p/2}\qquad(q=1,2,3,4).$$</div>
<p><em>Proof.</em> Fix $r,C$ and suppress their indices. Since $0\leq Y\leq X$, the factorization of $X^q-Y^q$ gives $X^q-Y^q\leq qX^{q-1}Z$, where $Z=X-Y$. Cauchy–Schwarz, applied to $X^{q-1}\sqrt Z$ and $\sqrt Z$, yields</p>
<div class="math-display">$$\mathbb E(X^{q-1}Z)\leq\bigl(\mathbb E[X^{2q-2}Z]\,\mathbb E Z\bigr)^{1/2}\leq\bigl(m_{2q-1}(r)\,\mathbb E Z\bigr)^{1/2}.$$</div>
<p>Use the spatial estimate for $\mathbb E Z$, then divide by $m_q(r)$. For $q=1$ the moment ratio equals one. Choose $C$ large enough that all four right-hand sides are at most $\varepsilon/(1+\varepsilon)$. Rearranging gives (wCL).</p>
<p>The uniform moment ratios are additional assumptions, not consequences of the definition of (CL). For example, the two-sided moment scales $m_s(r)\asymp z(r)^{s-a}$ for $s=1,\ldots,7$, with fixed $0&lt;a&lt;1$ and constants uniform in $r$, supply them: the powers in $m_{2q-1}\chi/m_q^2$ cancel. The <a href="/articles/cutoff-scaling/#section-volume">uniform volume-tail cutoff bounds</a> are one way to obtain those scales. Establishing such bounds for a particular model remains a separate problem.</p>

## From localized damping to full moment ratios {#section-damping}

<a id="tag-0WAE" data-assertion="proposition" data-title="Localized exponential damping controls the full moment ratios"></a>
<p>Let $0\leq Y_r\leq X_r$ and write $m_p(r)=\mathbb E X_r^p$. Suppose the first four moments are finite and positive. Let $Q(r)&gt;0$, and suppose constants $A,b,L&gt;0$, independent of $r$, satisfy</p>
<div class="math-display">$$\mathbb P(Y_r\geq tQ(r))\leq A e^{-bt}\mathbb P(Y_r\geq Q(r))\qquad(t\geq1),$$</div>
<div class="math-display">$$m_j(r)\leq L\mathbb E Y_r^j\qquad(j=2,3,4).$$</div>
<p>There is a finite constant $D$, depending only on $A,b,L$, for which</p>
<div class="math-display">$$m_2\leq DQm_1,\qquad m_3\leq DQ^2m_1,\qquad m_3\leq DQm_2,\qquad m_4\leq DQ^2m_2.$$</div>
<p><em>Proof.</em> The <a href="/tag/BZDZ/">rooted damping estimate</a> gives $\mathbb E Y_r^{p+q}\leq D_{p,q}Q(r)^q\mathbb E Y_r^p$. Apply it for $(p,q)=(1,1),(1,2),(2,1),(2,2)$, use localization at order $p+q$, and then $Y_r\leq X_r$. Take $D=L\max D_{p,q}$ over these four pairs.</p>
<p>For cutoff clusters, (wCL) with $\varepsilon=1$ supplies one fixed $C\geq1$ and $L=2$, with $Y_r=|K_r\cap B_{Cr}|$. If the rooted damping bound holds at the window quantile, take $Q(r)=M(r,Cr)$. Under an increasing coupling of the cutoff laws, $M(r,Cr)\leq M(Cr,Cr)$. Thus the estimates retain one fixed radius factor; no limit in $C$ is taken while $r$ varies.</p>
<p>This direction of implication is distinct from the earlier sufficient criterion for (wCL). Here localization and rooted damping are inputs, and the conclusion concerns moment ratios. It must not be used together with that criterion as a circular proof of localization.</p>

## Why the higher moments matter {#section-example}

<a id="tag-IBK7" data-assertion="proposition" data-title="Spatial localization alone need not localize the second volume moment"></a>
<p>There is a family of finite random subsets on a countable metric space satisfying (CL), with every volume moment finite at every radius, for which (wCL) fails already at $q=2$.</p>
<p>To construct it, let $N_n=\lceil e^{n^2}\rceil$ for integers $n\geq2$. Attach $N_n$ leaves to a root by edges of length $n^2$, for each $n$, and use the resulting tree metric on the root and leaves. At radius $r=n$, let $K_n$ consist of the root and all $N_n$ leaves in that group with probability $a_n=N_n^{-3/2}$, and otherwise just the root. At every other radius take the root alone. This defines random subsets, not an independent-bond model.</p>
<p>Every set in each law is finite. At an integer radius, $\chi_n=1+N_n^{-1/2}$ and</p>
<div class="math-display">$$\frac{\xi_p(n)^p}{n^p}=\frac{N_n^{-1/2}n^p}{1+N_n^{-1/2}}.$$</div>
<p>For every fixed $p&gt;0$ this is bounded in $n$, since exponential decay dominates $n^p$; at other radii it is zero. Thus (CL) holds for all finite $p$. But if $n&gt;C$, all the leaves used at radius $n$ lie outside $B_{Cn}$, so $|K_n\cap B_{Cn}|=1$, whereas</p>
<div class="math-display">$$m_2(n)=1+a_n\bigl((N_n+1)^2-1\bigr)=1+N_n^{1/2}+2N_n^{-1/2}\longrightarrow\infty.$$</div>
<p>No fixed $C$ can therefore give the $q=2$ comparison even with $\varepsilon=1$. Rare large sets have negligible expected spatial mass but dominate the second volume moment. Additional structure of a percolation model may rule this out; the definition of (CL) alone does not.</p>

## Source scope {#section-source}

<p>The definitions record S037–S038 of the pinned notes, lines 5661–5698, with finite moments and the range $r\geq1$ made explicit so that the ratios and comparisons are meaningful. S039, lines 5700–5715, describes (wCL) as a separate input supplied by model-specific localization technology. The conditional argument above gives one sufficient moment-ratio criterion; it is not attributed to that passage as a proof of its model-specific claim. Neither the quoted Sak upper bound nor a sharp crossover boundary is established here.</p>

## Quoted localization regimes {#section-quoted-regimes}

<p>The notes' <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L4288">Euclidean two-point summary (S028)</a> and <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L5717">localization summary (S040)</a> quote model-specific results. They are not additional hypotheses of the conditional propositions above. In particular, the following source descriptions must be kept distinct.</p>

<ul><li>S028 distinguishes averaged two-point bounds from pointwise estimates. It quotes pointwise comparisons only where the required localization and regularity inputs are available, including the non-perturbative $\alpha&lt;1$ range and separately supplied perturbative regimes. An averaged estimate alone is not recorded here as a pointwise estimate.</li>
<li>S040 describes $\alpha&lt;1$ as a sufficient localization range for the Euclidean power-law models treated by its references, together with two-sided kernel regularity and a non-trivial critical point. Its passage from (CL) to a pointwise upper bound also calls for regularity inputs. It does not state that the definition of (CL), by itself, proves that bound for every kernel.</li>
<li>The following paragraph discusses the larger $\alpha&lt;2$ spatial range in the high- and critical-effective-dimensional models covered by the cutoff theory. That model qualification cannot be dropped or applied to every pair $(d,\alpha)$. The expected Sak crossover in low dimensions is presented separately as a prediction.</li>
<li>The matching pointwise lower bound is attributed to separate arguments. The notes also distinguish failure of (CL) in some short-range regimes from a theorem identifying the entire expected crossover boundary.</li></ul>

<p>These are locators and scope distinctions for the quoted passages, not a correspondence certificate for their external references. Before assigning a permanent theorem tag to either summary, the source theorem and revision must fix the dimension and parameter ranges, kernel regularity, critical-point assumptions, cutoff convention and uniformity of its constants. The present summaries do not spell out all those data. The conditional results in this article and the <a href="/articles/cutoff-hydrodynamics/">cutoff hydrodynamics article</a> therefore retain their stated inputs; neither passage closes those proof obligations.</p>

<p>Candidate locators are now available in the <a href="https://arxiv.org/pdf/2508.18808v1">versioned PDF of Long-range II</a>: kernel assumptions on p. 3 and §II.1.1, (CL) in Definition II.1.3, and Theorems II.1.5 and II.1.7 on pp. 10–11. The kernel is radial and decreasing, with $|J'(r)|=C(1+\delta_r)r^{-d-\alpha-1}$, $\delta_r\to0$ and $\int_{r_0}^\infty|\delta_r|\,dr/r&lt;\infty$; footnote 3 relaxes the rate assumption for low-dimensional results. These locators narrow the correspondence work; they do not establish that every notes formulation has identical hypotheses.</p>

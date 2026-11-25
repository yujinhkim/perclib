---
{
  "id": "mesoscopic-tail-transfer",
  "title": "From cutoff mass to a full volume tail",
  "subtitle": "Small-cluster negligibility and a quantitative ghost comparison",
  "kind": "method",
  "category": "Critical phenomena",
  "summary": "Uniform negligibility of small cutoff clusters makes the cutoff-to-full comparison contractive. First and second moment bounds then yield two-sided power bounds for the full cluster tail, without assuming convergence to a limiting cluster law.",
  "context": ["Cutoff sizes $X_r$ are nonnegative with finite first and second moments.", "The cutoff mass scale is $r^\\kappa$, with $0<\\alpha<\\kappa$ and mean of order $r^\\alpha$.", "Negligibility and the cutoff-to-full comparison are explicit inputs, not consequences of moment orders alone."],
  "related": ["cutoff-hydrodynamics", "cutoff-localization", "size-biased-laws", "ghost-fields", "regular-variation"],
  "sourceIds": ["notes", "hutchcroft-lrp-2"],
  "aliases": ["mesoscopic negligibility", "truncated first moment", "tail extraction", "low-dimensional volume tail"],
  "prototypeUses": []
}
---

## The uniform input {#section-input}

<a id="tag-QMN5" data-assertion="definition" data-title="Mesoscopic negligibility relative to the cutoff mass scale"></a>
<p>Let $X_r\geq0$ have finite positive mean $m_1(r)$, for all sufficiently large $r$, and let $\kappa&gt;0$. Mesoscopic negligibility at scale $r^\kappa$ means</p>
<div class="math-display">$$\lim_{\delta\downarrow0}\limsup_{r\to\infty}\frac{\mathbb E\min(X_r,\delta r^\kappa)}{m_1(r)}=0.$$</div>
<p>The large-scale limit is taken before the small-$\delta$ limit. For each fixed $r$, sending $\delta$ to zero would give a trivial assertion and would provide no uniform control on the family. The truncated expectation includes a contribution $\delta r^\kappa$ from every cluster above that size; it is not just $\mathbb E[X_r\mathbf1_{\{X_r\leq\delta r^\kappa\}}]$.</p>

## The finite-model truncated differential inequality {#section-finite-russo}

<a id="tag-MIJ7" data-assertion="proposition" data-title="Truncated Russo bound on a finite transitive bond model"></a>
<p>Let $V$ be a finite nonempty vertex set, and let a group act transitively on $V$. For each unordered pair of distinct vertices, let $\lambda_{xy}(t)\geq0$ be continuously differentiable on an open interval $I$, invariant under the group, with $\lambda_{xy}'(t)\geq0$. Open the pairs independently with probabilities $1-e^{-\lambda_{xy}(t)}$. Fix a root $o$, and put</p>
<div class="math-display">$$a(t)=\sum_{y\ne o}\lambda_{oy}'(t),\qquad T_m(t)=\mathbb E_t\min(|K_o|,m)\quad(m&gt;0).$$</div>
<p>Then $T_m$ is continuously differentiable and</p>
<div class="math-display">$$0\leq T_m'(t)\leq a(t)T_m(t)^2.$$</div>
<p>The row $a(t)$ is independent of the root. The bound holds for real truncations $m&gt;0$, including $m&lt;1$.</p>
<p><em>Proof.</em> Fix $t$ and write $f(s)=\min(s,m)$ and $w_{xy}=\lambda_{xy}'(t)$. Finite-product differentiation gives the expected change from opening each edge, multiplied by $w_{xy}e^{-\lambda_{xy}(t)}$. Equivalently, retain the edge's closed indicator inside the expectation and multiply by $w_{xy}$. An edge matters only when it joins the root cluster to another cluster. Thus</p>
<div class="math-display">$$T_m'(t)=\mathbb E_t\sum_{x\in K_o}\sum_{y\notin K_o}w_{xy}\bigl[f(|K_o|+|K_y|)-f(|K_o|)\bigr].$$</div>
<p>There is no factor of two: each contributing unordered edge has exactly one endpoint in $K_o$. Transitivity and finite double counting move its endpoint to the root:</p>
<div class="math-display">$$T_m'(t)=\mathbb E_t\left[|K_o|\sum_{y\notin K_o}w_{oy}\bigl[f(|K_o|+|K_y|)-f(|K_o|)\bigr]\right].$$</div>
<p>To see the equality directly, average each expression over all roots. In a fixed configuration, a cluster $A$ contributes its boundary sum once for each of its $|A|$ possible roots. Both averages therefore agree configuration by configuration. Invariance makes their expectations independent of the chosen root.</p>
<p>The elementary inequality</p>
<div class="math-display">$$u\bigl[f(u+v)-f(u)\bigr]\leq f(u)f(v)\qquad(u,v\geq0)$$</div>
<p>now bounds the last expectation by $\mathbb E_t[f(|K_o|)\sum_{y\notin K_o}w_{oy}f(|K_y|)]$. Condition on $K_o=A$. The event determining this cluster uses only edges within $A$ and from $A$ to its complement; edges wholly outside $A$ retain their independent laws. For $y\notin A$, its cluster is the cluster in the induced model outside $A$, which is stochastically dominated by its cluster in the full model. Hence</p>
<div class="math-display">$$\mathbb E_t\!\left[\sum_{y\notin K_o}w_{oy}f(|K_y|)\,\middle|\,K_o=A\right]\leq\sum_{y\notin A}w_{oy}T_m(t)\leq a(t)T_m(t).$$</div>
<p>Taking expectations proves the upper bound; every summand in the derivative formula is nonnegative. Continuous differentiability follows from the finite product formula. The merge inequality used above is proved just below.</p>
<p>This finite result does not justify an infinite-volume derivative by itself. Nor does restricting an infinite transitive model to an arbitrary finite box preserve the transitivity used in the double counting. A passage to the cutoff model must supply its own limiting or mass-transport argument and the required domination.</p>

## Passing to a countable model {#section-countable-russo}

<a id="tag-D7A5" data-assertion="theorem" data-title="Countable truncated Russo bound under local summable domination"></a>
<p>Let a group act transitively on a countable nonempty set $V$ and satisfy the <a href="/tag/N0HM/">mass-transport property</a>. On an open interval $I$, let $\lambda_{xy}:I\to[0,\infty)$, for unordered pairs of distinct vertices, be locally absolutely continuous, nondecreasing and invariant under the action. For every compact interval $[u,v]\subset I$, assume there is a symmetric invariant array $W_{xy}\geq0$ such that</p>
<div class="math-display">$$0\leq\lambda_{xy}'(t)\leq W_{xy}\quad\text{for a.e. }t\in[u,v],\qquad R_W=\sum_{y\ne o}W_{oy}&lt;\infty.$$</div>
<p>Open the pairs independently with probabilities $1-e^{-\lambda_{xy}(t)}$, and suppose $\chi(t)=\mathbb E_t|K_o|&lt;\infty$ for every $t\in I$. For each fixed real $m&gt;0$, the function $T_m(t)=\mathbb E_t\min(|K_o|,m)$ is locally absolutely continuous and satisfies</p>
<div class="math-display">$$0\leq T_m'(t)\leq a(t)T_m(t)^2\quad\text{a.e.},\qquad a(t)=\sum_{y\ne o}\lambda_{oy}'(t).$$</div>
<p><em>Proof.</em> Fix $[u,v]\subset I$ and exhaust $V$ by finite sets containing $o$. In the model induced by the $n$th set, write $K_x^{(n)}$ for a cluster, $T_m^{(n)}$ for the truncated mean, and $f(s)=\min(s,m)$. Finite-product differentiation gives the integrated identity</p>
<div class="math-display">$$T_m^{(n)}(t)-T_m^{(n)}(s)=\int_s^t\mathbb E_z\sum_{x\in K_o^{(n)}}\sum_{y\notin K_o^{(n)}}\lambda_{xy}'(z)\bigl[f(|K_o^{(n)}|+|K_y^{(n)}|)-f(|K_o^{(n)}|)\bigr],dz,$$</div>
<p>where both vertices in the sum belong to the finite set. This identity does not require that set to be transitive. Couple all configurations using uniform variables on the edges. At parameter $z\leq v$, the absolute value of each summand is at most</p>
<div class="math-display">$$mW_{xy}\mathbf1_{\{o\leftrightarrow x\text{ at parameter }v\}}.$$</div>
<p>The sum of its expectations is $mR_W\chi(v)&lt;\infty$, uniformly in $z$. At every fixed parameter, finiteness of susceptibility and countability imply that all clusters are finite almost surely. For each fixed pair $x,y$, its summand therefore converges to the full-volume summand: a finite connected cluster is eventually seen inside the exhaustion. Countably many locally absolutely continuous edge intensities also have a common full-measure set of differentiability. Dominated convergence in the edge sum, expectation and parameter integral gives</p>
<div class="math-display">$$T_m(t)-T_m(s)=\int_s^t D_m(z),dz,$$</div>
<p>with</p>
<div class="math-display">$$D_m(z)=\mathbb E_z\sum_{x\in K_o}\sum_{y\notin K_o}\lambda_{xy}'(z)\bigl[f(|K_o|+|K_y|)-f(|K_o|)\bigr].$$</div>
<p>In particular $T_m$ is absolutely continuous on $[u,v]$. It remains to bound its derivative in the transitive full-volume model.</p>
<p>Fix a parameter where the edge derivatives exist. For vertices $p,x$, send from $p$ to $x$ the expected nonnegative mass</p>
<div class="math-display">$$\mathbb E\left[\mathbf1_{\{x\in K_p\}}\sum_{y\notin K_p}\lambda_{xy}'\bigl[f(|K_p|+|K_y|)-f(|K_p|)\bigr]\right].$$</div>
<p>This mass is invariant under the diagonal group action. The total outgoing mass at $o$ is $D_m$; the incoming mass is</p>
<div class="math-display">$$\mathbb E\left[|K_o|\sum_{y\notin K_o}\lambda_{oy}'\bigl[f(|K_o|+|K_y|)-f(|K_o|)\bigr]\right].$$</div>
<p>Mass transport equates them. Apply $a[f(a+b)-f(a)]\leq f(a)f(b)$ and condition on the finite root cluster. Its complement retains its independent edge law, and its clusters are dominated by the full-model clusters. Tonelli and transitivity then give $D_m\leq a(t)T_m(t)^2$, exactly as in the finite proof. All terms are nonnegative, so no subtraction of infinite sums occurs.</p>
<p>For the Euclidean soft cutoff $\lambda_{xy}(r)=\beta\mathbf1_{\{|x-y|\leq r\}}[j(|x-y|)-j(r)]$, with fixed $\beta&gt;0$ and nonincreasing continuously differentiable $j$, the derivative is $-\beta j'(r)\mathbf1_{\{|x-y|&lt;r\}}$ almost everywhere. On a compact radius interval it is dominated by a bounded array of finite range. Provided every cutoff susceptibility on that interval is finite, the theorem applies with</p>
<div class="math-display">$$a(r)=\beta|j'(r)|\,\#\{y\ne o:|y-o|&lt;r\}\leq\beta|j'(r)|\,|B_r|.$$</div>
<p>The count excludes the diagonal. The kernel is continuous when a new distance enters the cutoff because its intensity starts at zero. Thus the truncation inequality used in the notes follows under these stated regularity and susceptibility assumptions; a finite interaction range alone does not supply the latter. For the normalized power-law cutoff, <a href="/tag/0CUF/">strict domination below the full endpoint</a> provides the relevant finiteness criterion.</p>

## The second moment and its collision correction {#section-second-moment}

<a id="tag-6H7C" data-assertion="theorem" data-title="Second-moment Russo identity and a truncated collision bound"></a>
<p>Under the hypotheses of the countable truncated Russo theorem, suppose also $m_3(t)=\mathbb E_t|K_o|^3&lt;\infty$ for every $t\in I$. Write $m_2(t)=\mathbb E_t|K_o|^2$, $w_{xy}(t)=\lambda_{xy}'(t)$ and $c(t)=\sup_{y\ne o}w_{oy}(t)$, with an empty supremum equal to zero. Then $m_2$ is locally absolutely continuous and, almost everywhere,</p>
<div class="math-display">$$m_2'(t)=3\sum_{y\ne o}w_{oy}(t)\mathbb E_t\bigl[|K_o|^2|K_y|\mathbf1_{\{o\not\leftrightarrow y\}}\bigr].$$</div>
<p>For every fixed $m&gt;0$, this gives</p>
<div class="math-display">$$m_2'(t)\geq3a(t)m_2(t)T_m(t)-3m c(t)m_3(t)\quad\text{a.e.}$$</div>
<p><em>Proof.</em> First justify differentiation by finite exhaustion, as for the truncated mean. On a compact parameter interval $[u,v]$, let $A=|K_o|$ and $B_y=|K_y|$ in the full model at the upper endpoint $v$. A dominating sum for the finite-volume derivative integrands is</p>
<div class="math-display">$$\sum_{x\in K_o}\sum_{y\ne x}W_{xy}(2AB_y+B_y^2).$$</div>
<p>Mass transport, followed by Hölder's inequality and transitivity, bounds its expectation by</p>
<div class="math-display">$$\sum_{y\ne o}W_{oy}\mathbb E_v(2A^2B_y+AB_y^2)\leq3R_Wm_3(v)&lt;\infty.$$</div>
<p>Indeed, move the endpoint $x$ to the root exactly as in the previous proof, and use $\mathbb E(A^2B_y),\mathbb E(AB_y^2)\leq m_3(v)$. Dominated convergence in the integrated finite-volume identity proves local absolute continuity and identifies the derivative with the full boundary sum. No finite box is assumed transitive.</p>
<p>At a fixed parameter, mass transport rewrites that boundary sum as</p>
<div class="math-display">$$\sum_{y\ne o}w_{oy}\mathbb E\bigl[(2A^2B_y+AB_y^2)\mathbf1_{\{o\not\leftrightarrow y\}}\bigr].$$</div>
<p>A second mass transport interchanges the root and $y$. Symmetry of $w$ shows that the summed $AB_y^2$ term equals the summed $A^2B_y$ term, proving the factor-three identity. The preceding domination makes every sum finite.</p>
<p>Replace $B_y$ in that identity by $\min(B_y,m)$. The <a href="/tag/X5SS/">Harris inequality</a>, applied first to bounded increasing truncations and then by monotone convergence, gives</p>
<div class="math-display">$$\mathbb E[A^2\min(B_y,m)]\geq m_2T_m.$$</div>
<p>Subtract the contribution from $\{o\leftrightarrow y\}$, on which $B_y=A$. The total amount subtracted is at most</p>
<div class="math-display">$$m\mathbb E\left[A^2\sum_{y\ne o}w_{oy}\mathbf1_{\{o\leftrightarrow y\}}\right]\leq mc\mathbb E[A^2(A-1)]\leq mc m_3.$$</div>
<p>Multiplying by three proves the lower bound. This argument controls the same-cluster contribution explicitly; it does not assume independence of clusters rooted at two fixed vertices.</p>
<p>For the soft cutoff above, write $N_r=\#\{y\ne o:|y-o|&lt;r\}$. Wherever $N_r&gt;0$, one has $a(r)=\beta|j'(r)|N_r$ and $c(r)=\beta|j'(r)|$. Suppose $N_r\geq v_0r^d$ and $m_3(r)\leq K r^\kappa m_2(r)$ at large radii. When $2\kappa=d+\alpha$, the lower bound becomes</p>
<div class="math-display">$$(\log m_2)'(r)\geq3a(r)\left(T_m(r)-\frac{K}{v_0}m r^{\alpha-\kappa}\right).$$</div>
<p>Thus the collision inequality needed below follows from a uniform third-to-second moment comparison, together with the stated regularity, susceptibility and moment-finiteness hypotheses. Rooted damping and localization are one route to such a comparison, but a largest-cluster quantile estimate alone does not establish it.</p>

## The finite-model moment hierarchy {#section-finite-hierarchy}

<a id="tag-C9Y8" data-assertion="theorem" data-title="All cluster-moment derivatives in a finite transitive intensity model"></a>
<p>Let a group act transitively on a nonempty finite vertex set $V$. On an open interval of parameters, let the finite nonnegative intensities $\lambda_t(u,v)=\lambda_t(v,u)$ be continuously differentiable, nondecreasing and invariant under that action. Give distinct pairs independent bond probabilities $1-e^{-\lambda_t(u,v)}$. Write $w_t(u,v)=\partial_t\lambda_t(u,v)$, $a(t)=\sum_{y\neq o}w_t(o,y)$ and $m_k(t)=\mathbb E_t|K_o|^k$. Then, for every integer $k\geq1$,</p>
<div class="math-display">$$m_k'(t)=\frac12\sum_{y\neq o}w_t(o,y)\,\mathbb E_t\!\left[\mathbf1_{\{o\not\leftrightarrow y\}}\sum_{j=1}^k\binom{k+1}{j}|K_o|^j|K_y|^{k+1-j}\right].$$</div>
<p>Moreover,</p>
<div class="math-display">$$0\leq m_k'(t)\leq\frac{a(t)}2\sum_{j=1}^k\binom{k+1}{j}m_j(t)m_{k+1-j}(t)=a(t)\sum_{\ell=0}^{k-1}\binom{k}{\ell}m_{\ell+1}(t)m_{k-\ell}(t).$$</div>
<p><em>Proof.</em> For each configuration, sum the rooted observable over $V$:</p>
<div class="math-display">$$\sum_{v\in V}|K_v|^k=\sum_{C\text{ a cluster}}|C|^{k+1}.$$</div>
<p>Opening an edge between distinct clusters of sizes $A,B$ changes the right side by $(A+B)^{k+1}-A^{k+1}-B^{k+1}$; an edge within one cluster changes nothing. Finite-coordinate differentiation multiplies this increment by $w_t(u,v)e^{-\lambda_t(u,v)}$, with the edge forced closed. Equivalently, average the increment over the original law with the distinct-cluster indicator: distinct endpoints already force this edge closed, supplying exactly the factor $e^{-\lambda_t(u,v)}$.</p>
<p>Transitivity makes the expectation of the left side $|V|m_k(t)$. Replace the sum over unordered edges by half the sum over ordered distinct pairs. Invariance makes the sum with first endpoint $u$ independent of $u$, cancelling the factor $|V|$. Expanding the merger increment proves the identity.</p>
<p>To bound a summand, condition on $K_o=C$. On $y\notin C$, the cluster of $y$ is determined by the unchanged independent bonds outside $C$. Coupling these bonds to the full model bounds its conditional moment of order $k+1-j$ by $m_{k+1-j}(t)$. Hence</p>
<div class="math-display">$$\mathbb E_t[|K_o|^j|K_y|^{k+1-j}\mathbf1_{\{o\not\leftrightarrow y\}}]\leq m_j(t)m_{k+1-j}(t).$$</div>
<p>Insert this bound and sum the rates. For the last equality, pair the coefficients with indices $j$ and $k+1-j$ and use Pascal's identity. All sums are finite; no infinite-volume differentiation is used.</p>
<p>The first three upper bounds are $m_1'\leq am_1^2$, $m_2'\leq3am_1m_2$ and $m_3'\leq a(4m_1m_3+3m_2^2)$. They explain the binomial coefficients in the <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L4542">notes' moment hierarchy</a>. The exact finite identity does not replace the two-cluster expectation by a product. An infinite-volume hierarchy needs justified differentiation and summation limits; an asymptotically closed hierarchy additionally needs negligible factorization errors.</p>

## The countable moment hierarchy {#section-countable-hierarchy}

<a id="tag-09EI" data-assertion="theorem" data-title="Countable all-order moment flow under summable local domination"></a>
<p>Assume the hypotheses of <a href="/tag/D7A5/">D7A5</a>: a countable transitive model satisfying mass transport, nondecreasing invariant locally absolutely continuous intensities, a symmetric invariant summable derivative envelope on each compact parameter interval, and finite susceptibility. Fix an integer $k\geq1$ and suppose $m_{k+1}(t)=\mathbb E_t|K_o|^{k+1}&lt;\infty$ throughout the interval. Then $m_k$ is locally absolutely continuous and the exact derivative identity and upper bound of <a href="/tag/C9Y8/">C9Y8</a> hold almost everywhere, with the same definitions of $w_t$ and $a(t)$.</p>
<p><em>Proof.</em> Fix a compact parameter interval $[u,v]$ and its envelope $W$, with row sum $R_W$. In a finite induced subgraph, differentiate the root moment and integrate in the parameter. Its derivative integrand is the expectation of</p>
<div class="math-display">$$\sum_{x\in K_o^{(n)}}\sum_{y\notin K_o^{(n)}}w_t(x,y)\left[(|K_o^{(n)}|+|K_y^{(n)}|)^k-|K_o^{(n)}|^k\right],$$</div>
<p>where both endpoints belong to the finite subgraph. This is the finite boundary-edge formula; it does not require the subgraph to be transitive.</p>
<p>Couple the configurations monotonically in volume and parameter. Let $A=|K_o|$ and $B_y=|K_y|$ in the full model at $v$. A dominating sum, independent of the finite subgraph and of $t\in[u,v]$, is</p>
<div class="math-display">$$\sum_{x\in K_o}\sum_{y\neq x}W_{xy}\sum_{j=1}^k\binom{k}{j}A^{k-j}B_y^j.$$</div>
<p>Move $x$ to the receiving root by mass transport, as in D7A5. The expectation of this sum is</p>
<div class="math-display">$$\sum_{y\neq o}W_{oy}\sum_{j=1}^k\binom{k}{j}\mathbb E_v[A^{k-j+1}B_y^j]\leq(2^k-1)R_Wm_{k+1}(v)&lt;\infty.$$</div>
<p>For the inequality, apply Hölder with exponents $(k+1)/(k-j+1)$ and $(k+1)/j$, then use transitivity to identify both moments of order $k+1$.</p>
<p>Finite susceptibility makes every cluster finite almost surely. At each fixed parameter the finite-volume summands therefore converge to the full-volume summands. Countability gives a common almost-everywhere set of differentiability for the intensities. Dominated convergence in the edge sum, expectation and parameter integral yields an integral identity for $m_k$, proving local absolute continuity.</p>
<p>Apply mass transport to its full boundary sum. Writing $A=|K_o|$ and $B_y=|K_y|$ now at the current parameter, the derivative becomes</p>
<div class="math-display">$$\sum_{y\neq o}w_t(o,y)\,\mathbb E_t\!\left[\mathbf1_{\{o\not\leftrightarrow y\}}A\bigl((A+B_y)^k-A^k\bigr)\right].$$</div>
<p>A second mass transport exchanges the endpoints. Symmetry of $w_t$ allows us to average the last expression with the one having $A$ and $B_y$ interchanged. Their averaged polynomial is $[(A+B_y)^{k+1}-A^{k+1}-B_y^{k+1}]/2$, giving the exact hierarchy. The same domination makes the sums finite. Finally, condition on the finite root cluster and dominate each outside-cluster moment by its full-model value, exactly as in C9Y8, to obtain the upper bound.</p>
<p>For the soft cutoff, <a href="/tag/0CUF/">0CUF</a> supplies moment finiteness when its subcritical-susceptibility hypothesis holds; the derivative envelope has finite range on compact radius intervals. This gives the exact countable hierarchy in that setting. It still does not show that the two-cluster terms approach products of moments: the error estimates in the notes remain a separate probabilistic input.</p>

## Relative errors in the first two moment equations {#section-moment-errors}

<a id="tag-NJF3" data-assertion="proposition" data-title="Russo moment deficits are controlled by the third and fourth moments"></a>
<p>Under the hypotheses of the countable truncated Russo theorem, suppose $m_4(t)=\mathbb E_t|K_o|^4&lt;\infty$ for every $t\in I$. With $a(t)=\sum_{y\ne o}\lambda_{oy}'(t)$ and $c(t)=\sup_{y\ne o}\lambda_{oy}'(t)$, the first two moments are locally absolutely continuous and satisfy, almost everywhere,</p>
<div class="math-display">$$a m_1^2-cm_3\leq m_1'\leq a m_1^2,\qquad 3a m_1m_2-3cm_4\leq m_2'\leq3a m_1m_2.$$</div>
<p>Both derivatives are nonnegative. Wherever $a&gt;0$, one may therefore write</p>
<div class="math-display">$$m_1'=a m_1^2(1-e_1),\qquad m_2'=3a m_1m_2(1-e_2),$$</div>
<p>where $e_1,e_2\in[0,1]$ and</p>
<div class="math-display">$$e_1\leq\frac{c m_3}{a m_1^2},\qquad e_2\leq\frac{c m_4}{a m_1m_2}.$$</div>
<p><em>Proof.</em> The dominated-exhaustion argument for the second moment also applies to the first: its edge increment is smaller, and the third moment at the upper endpoint of each compact interval already dominates the integrated sums. Mass transport gives, with $A=|K_o|$ and $B_y=|K_y|$,</p>
<div class="math-display">$$m_1'=\sum_{y\ne o}w_{oy}\mathbb E[AB_y\mathbf1_{\{o\not\leftrightarrow y\}}],\qquad m_2'=3\sum_{y\ne o}w_{oy}\mathbb E[A^2B_y\mathbf1_{\{o\not\leftrightarrow y\}}].$$</div>
<p>Condition on $K_o$. Every outside cluster has conditional mean at most $m_1$, so the two expressions are at most $a m_1^2$ and $3a m_1m_2$ respectively. Harris association gives $\mathbb E AB_y\geq m_1^2$ and $\mathbb E A^2B_y\geq m_2m_1$, by truncation if necessary. On the same-cluster event $B_y=A$, and</p>
<div class="math-display">$$\sum_{y\ne o}w_{oy}\mathbb E[A^j\mathbf1_{\{o\leftrightarrow y\}}]\leq c\mathbb E[A^j(A-1)]\leq c m_{j+1}\qquad(j=2,3).$$</div>
<p>Subtract these contributions to obtain the lower bounds. The displayed relative errors follow by division; nonnegativity of the derivative and its upper bound place each error in $[0,1]$.</p>
<p>For a soft cutoff, $c/a=1/N_r$ whenever $a&gt;0$. The <a href="/tag/0WAE/">localized moment ratios</a> therefore imply $e_i(r)\leq DQ(r)^2/[N_r m_1(r)]$. If $N_r\succeq r^d$, $m_1(r)\succeq r^\alpha$ and $Q(r)\leq M_{Cr}$ for fixed $C$, this is precisely an error bound of order $M_{Cr}^2/r^{d+\alpha}$. The same moment-ratio result gives $m_2(r)\preceq M_{Cr}m_1(r)$.</p>

## A collision bound at every order {#section-all-order-errors}

<a id="tag-XXTP" data-assertion="proposition" data-title="All-order moment factorization error from a collision bound"></a>
<p>Under the hypotheses of <a href="/tag/D7A5/">D7A5</a>, fix an integer $k\geq1$ and assume $m_{k+2}(t)&lt;\infty$ throughout the parameter interval. Write $c(t)=\sup_{y\ne o}w_{oy}(t)$, with an empty supremum equal to zero, and set</p>
<div class="math-display">$$H_k(t)=\frac{a(t)}2\sum_{j=1}^k\binom{k+1}{j}m_j(t)m_{k+1-j}(t).$$</div>
<p>Then, almost everywhere,</p>
<div class="math-display">$$0\leq H_k-m_k'\leq(2^k-1)c\bigl(m_{k+2}-m_{k+1}\bigr)\leq(2^k-1)c m_{k+2}.$$</div>
<p>Where $a&gt;0$, the relative error $e_k=1-m_k'/H_k$ belongs to $[0,1]$ and satisfies</p>
<div class="math-display">$$e_k\leq\frac{(2^k-1)c m_{k+2}}{H_k}.$$</div>
<p><em>Proof.</em> Fix a parameter where the <a href="/tag/09EI/">countable hierarchy</a> holds. Put $A=|K_o|$, $B_y=|K_y|$ and $l=k+1-j$. Conditioning on the root cluster gives</p>
<div class="math-display">$$\mathbb E[A^jB_y^l\mathbf1_{\{o\not\leftrightarrow y\}}]\leq m_jm_l.$$</div>
<p>On the other hand, Harris association, first for bounded truncations and then by monotone convergence, gives $\mathbb E A^jB_y^l\geq m_jm_l$. These expectations are finite by Hölder's inequality and the assumed moment bound. On $\{o\leftrightarrow y\}$ one has $B_y=A$, so</p>
<div class="math-display">$$0\leq m_jm_l-\mathbb E[A^jB_y^l\mathbf1_{\{o\not\leftrightarrow y\}}]\leq\mathbb E[A^{k+1}\mathbf1_{\{o\leftrightarrow y\}}].$$</div>
<p>After multiplication by $w_{oy}$ and summation over $y\ne o$, the right side is at most $c\mathbb E[A^{k+1}(A-1)]$. Insert this bound in the exact hierarchy and use $\tfrac12\sum_{j=1}^k\binom{k+1}{j}=2^k-1$. Nonnegativity of $m_k'$ gives $e_k\leq1$; the remaining claims follow by division.</p>
<p>For the soft cutoff, $c/a=1/N_r$ wherever $a&gt;0$. The displayed estimate therefore gives an explicit sufficient condition for factorization at any fixed order. For example, suppose independently that, for $1\leq j\leq k+2$,</p>
<div class="math-display">$$m_j(r)\asymp\chi(r)^{2j-1},\qquad \chi(r)=m_1(r),\qquad N_r\asymp r^d,\qquad\chi(r)\asymp r^\alpha.$$</div>
<p>Then $H_k/a\asymp\chi^{2k}$ and $m_{k+2}\asymp\chi^{2k+3}$, so $e_k(r)=O(r^{3\alpha-d})$ almost everywhere. In particular, if $d&gt;3\alpha$, the hierarchy closes asymptotically at this fixed order. This implication does not establish the moment orders used in its premise; using the closed hierarchy to obtain them would require a separate bootstrap. At $d=3\alpha$ the bound alone gives no vanishing error and no logarithmic asymptotic. The distinction is the one needed in the <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L4534">notes' mean-field moment flow</a>.</p>

## Propagating a truncated mean backwards in scale {#section-truncation}

<a id="tag-OP4X" data-assertion="proposition" data-title="A reciprocal differential inequality propagates a truncated mean"></a>
<p>Let $T$ be positive and locally absolutely continuous on $[r_0,R]$, and suppose $a\geq0$ is integrable there and $T'\leq aT^2$ almost everywhere. Then, for $r_0\leq\ell\leq R$,</p>
<div class="math-display">$$T(\ell)\geq\left(\frac1{T(R)}+\int_\ell^R a(s)\,ds\right)^{-1}.$$</div>
<p>If $\alpha,A,\varepsilon&gt;0$, $a(s)\leq As^{-\alpha-1}$ and $T(R)\geq\varepsilon R^\alpha$, this gives</p>
<div class="math-display">$$T(\ell)\geq\frac{\ell^\alpha}{A/\alpha+(\varepsilon^{-1}-A/\alpha)(\ell/R)^\alpha}.$$</div>
<p>The denominator is positive: it is a convex combination of $A/\alpha$ and $\varepsilon^{-1}$.</p>
<p><em>Proof.</em> The reciprocal is locally absolutely continuous and $(1/T)'=-T'/T^2\geq-a$ almost everywhere. Integrating from $\ell$ to $R$ gives the first inequality. For the second, integrate the power and use the lower bound at $R$.</p>
<p>The notes apply this to $T_m(r)=\mathbb E\min(|K|,m)$ with the truncation $m$ fixed throughout the interval. The elementary merge inequality behind that application is</p>
<div class="math-display">$$a\bigl(\min(a+b,m)-\min(a,m)\bigr)\leq\min(a,m)\min(b,m)\qquad(a,b,m\geq0).$$</div>
<p>If $a\geq m$, the left side is zero. Otherwise it is $a\min(b,m-a)\leq a\min(b,m)$. The finite transitive proposition above obtains the differential inequality by Russo differentiation and conditioning on the root cluster. The countable theorem supplies the corresponding justification under summable derivative domination and finite susceptibility. One must not differentiate a truncation that changes with $r$ as though it were fixed.</p>

## Negligibility from fixed-truncation differential inequalities {#section-negligibility}

<a id="tag-KKGL" data-assertion="theorem" data-title="Truncated moment inequalities force mesoscopic negligibility"></a>
<p>Let $0&lt;\alpha\leq\kappa&lt;2\alpha$. For $r\geq r_0&gt;0$, let $X_r\geq0$ have finite first and second moments, and write</p>
<div class="math-display">$$m_1(r)=\mathbb E X_r,\qquad m_2(r)=\mathbb E X_r^2,\qquad T_m(r)=\mathbb E\min(X_r,m).$$</div>
<p>Suppose $m_1(r)\asymp r^\alpha$ and, for constants $0&lt;b\leq B&lt;\infty$,</p>
<div class="math-display">$$br^{\alpha+\kappa}\leq m_2(r)\leq Br^{\alpha+\kappa}\qquad(r\geq r_0).$$</div>
<p>Assume $m_2$ and every fixed-truncation function $T_m$, $m&gt;0$, are positive and locally absolutely continuous. Let $a$ be a positive measurable function with $a(r)\sim a_0r^{-\alpha-1}$ for some $a_0&gt;0$. Suppose a constant $C\geq0$, independent of $m$ and $r$, satisfies, for every $m&gt;0$ and almost every $r\geq r_0$,</p>
<div class="math-display">$$T_m'(r)\leq a(r)T_m(r)^2,\qquad (\log m_2)'(r)\geq3a(r)\bigl(T_m(r)-Cm r^{\alpha-\kappa}\bigr).$$</div>
<p>Then mesoscopic negligibility holds at scale $r^\kappa$.</p>
<p><em>Proof.</em> Fix $\varepsilon&gt;0$. We will find $\delta&gt;0$ for which $T_{\delta R^\kappa}(R)&lt;\varepsilon R^\alpha$ at every sufficiently large $R$. Put $k=\alpha+\kappa$ and choose $\eta\in(0,1)$ so that $\mu=3\alpha(1-\eta)^2&gt;k$. Choose positive constants $a_-&lt;a_0&lt;a_+$ close enough that $a_-/a_+&gt;1-\eta$. Beyond a fixed radius,</p>
<div class="math-display">$$a_-t^{-\alpha-1}\leq a(t)\leq a_+t^{-\alpha-1}.$$</div>
<p>Choose $\lambda\in(0,1)$ so small that, with $D=(a_+/\alpha+\varepsilon^{-1}\lambda^\alpha)^{-1}$, one has $a_-D\geq\alpha(1-\eta)$. Next choose $L&gt;1$ with $L^{\mu-k}&gt;B/b$, and put $q=\lambda/L$. Finally choose $\delta&gt;0$ so small that $C\delta q^{-\kappa}\leq\eta D$; if $C=0$, any positive $\delta$ satisfies this last requirement.</p>
<p>Suppose now that $R$ is large and $T_m(R)\geq\varepsilon R^\alpha$ for the fixed number $m=\delta R^\kappa$. The reciprocal estimate, applied with this same $m$ throughout the interval, gives for $qR\leq t\leq\lambda R$,</p>
<div class="math-display">$$\frac1{T_m(t)}\leq\varepsilon^{-1}R^{-\alpha}+\frac{a_+}{\alpha}(t^{-\alpha}-R^{-\alpha})\leq D^{-1}t^{-\alpha}.$$</div>
<p>Consequently $T_m(t)\geq Dt^\alpha$, $a(t)T_m(t)\geq\alpha(1-\eta)/t$, and</p>
<div class="math-display">$$Cm t^{\alpha-\kappa}=C\delta(R/t)^\kappa t^\alpha\leq C\delta q^{-\kappa}t^\alpha\leq\eta T_m(t).$$</div>
<p>The second differential inequality therefore gives $(\log m_2)'(t)\geq\mu/t$ almost everywhere on this interval. Integration and the two moment bounds imply</p>
<div class="math-display">$$B(\lambda R)^k\geq m_2(\lambda R)\geq m_2(qR)L^\mu\geq b(\lambda R)^kL^{\mu-k},$$</div>
<p>contrary to the choice of $L$. All constants were chosen before $R$, and taking $qR$ beyond the fixed radius justifies every estimate. Since truncation is increasing in $\delta$, the conclusion also holds for every smaller $\delta$. Dividing by the lower bound for $m_1(R)$ and then letting $\varepsilon\downarrow0$ proves the stated ordered limit.</p>
<p>The argument starts from one radius with excessive truncated mass; it does not assume that such radii already fill a long interval. The truncation $m=\delta R^\kappa$ is held fixed while differentiating in $t$. Exceptional null sets may depend on this fixed $m$, which suffices for the integration.</p>
<p>The hypotheses have a simple probabilistic witness: for $r\geq1$, let $X_r=r^\kappa$ with probability $r^{\alpha-\kappa}$ and zero otherwise. Then $m_1=r^\alpha$, $m_2=r^{\alpha+\kappa}$ and $T_m=r^{\alpha-\kappa}\min(r^\kappa,m)$. The differential inequalities hold with $a(r)=\alpha r^{-\alpha-1}$ and $C=1$: below the truncation transition the first is an equality, above it $T_m$ is nonincreasing, and the bracket in the second is always nonpositive. This witnesses the analytic assumptions, not their realization by a percolation model.</p>
<p>For $\kappa=(d+\alpha)/2$, the parameter range is $\alpha\leq d&lt;3\alpha$, and the error power $\alpha-\kappa$ is $(\alpha-d)/2$. The <a href="/tag/NS0Q/">all-scale quantile estimate</a>, together with its lower and upper moment comparisons, supplies the required two-sided order of $m_2$. The first truncated differential inequality follows from the countable theorem under its regularity and susceptibility assumptions. The second follows from the preceding collision bound once a uniform third-to-second moment comparison is supplied. Once they are available, the theorem below yields the full tail in the additional range $\alpha&lt;d$.</p>

<a id="tag-J5R6" data-assertion="proposition" data-title="First and second moment orders do not imply mesoscopic negligibility"></a>
<p>For any $0&lt;\alpha&lt;\kappa$ and $r\geq1$, let $p_r=r^{\alpha-\kappa}$ and let $X_r$ equal $r^\kappa$ with probability $p_r$ and $r^\alpha$ with probability $1-p_r$. Then</p>
<div class="math-display">$$\mathbb E X_r=(2-p_r)r^\alpha\sim2r^\alpha,\qquad \mathbb E X_r^2=r^{\alpha+\kappa}+(1-p_r)r^{2\alpha}\sim r^{\alpha+\kappa},$$</div>
<p>but</p>
<div class="math-display">$$\lim_{\delta\downarrow0}\lim_{r\to\infty}\frac{\mathbb E\min(X_r,\delta r^\kappa)}{\mathbb E X_r}=\frac12.$$</div>
<p><em>Proof.</em> For fixed $0&lt;\delta&lt;1$ and sufficiently large $r$, one has $r^\alpha\leq\delta r^\kappa&lt;r^\kappa$. The truncated mean is then $(1+\delta-p_r)r^\alpha$. Divide by $(2-p_r)r^\alpha$ and take the limits in the indicated order. This is a family of random variables, not a percolation counterexample; it identifies information missing from the moment orders alone.</p>

## A two-sided tail bound {#section-transfer}

<a id="tag-ZWQ3" data-assertion="theorem" data-title="Mesoscopic negligibility and a ghost comparison imply a full power-law tail"></a>
<p>Fix $0&lt;\alpha&lt;\kappa$. Suppose $X_r\geq0$, for $r\geq r_0$, has finite first and second moments satisfying, with constants $c_1,C_1,C_2&gt;0$,</p>
<div class="math-display">$$c_1r^\alpha\leq m_1(r)=\mathbb E X_r\leq C_1r^\alpha,\qquad \mathbb E X_r^2\leq C_2r^\kappa m_1(r).$$</div>
<p>Assume mesoscopic negligibility at scale $r^\kappa$. Let $T\in[0,\infty]$, define</p>
<div class="math-display">$$G(h)=\mathbb E[1-e^{-hT}],\qquad G_r(h)=\mathbb E[1-e^{-hX_r}],$$</div>
<p>with $e^{-h\infty}=0$ for $h&gt;0$, and suppose for some $D\geq0$, $h_0&gt;0$ and every $r\geq r_0$, $0&lt;h&lt;h_0$,</p>
<div class="math-display">$$G_r(h)\leq G(h)\leq G_r(h)+Dr^{-\alpha}\mathbb E[X_re^{-hX_r}]G(h).$$</div>
<p>Then $T$ is finite almost surely and, writing $\rho=1-\alpha/\kappa\in(0,1)$,</p>
<div class="math-display">$$G(h)\asymp h^\rho\quad(h\downarrow0),\qquad \mathbb P(T&gt;t)\asymp t^{-\rho}\quad(t\to\infty).$$</div>
<p>For integer-valued $T$, the tail estimate also holds for $\mathbb P(T\geq n)$. These are two-sided bounds, not an assertion that a limiting amplitude exists.</p>
<p><em>Proof.</em> First make the comparison error uniformly smaller than one. For fixed $\delta,\lambda&gt;0$ with $hr^\kappa=\lambda$, split at $X_r=\delta r^\kappa$ to obtain</p>
<div class="math-display">$$\frac{\mathbb E[X_re^{-hX_r}]}{m_1(r)}\leq\frac{\mathbb E\min(X_r,\delta r^\kappa)}{m_1(r)}+e^{-\lambda\delta}.$$</div>
<p>If $D&gt;0$, choose $\delta$ so that the first term is eventually at most $1/(4DC_1)$, and then fix $\lambda$ large enough that $e^{-\lambda\delta}\leq1/(4DC_1)$. For sufficiently small $h$, take $r=(\lambda/h)^{1/\kappa}$; this eventually exceeds the scale required for that fixed $\delta$. The error coefficient is at most $1/2$, so</p>
<div class="math-display">$$G(h)\leq2G_r(h)\leq2h m_1(r)\leq2C_1\lambda^{\alpha/\kappa}h^\rho.$$</div>
<p>If $D=0$, the same upper bound follows directly with $\lambda=1$. In particular $G(h)\to0$, which implies $\mathbb P(T=\infty)=0$ by bounded convergence.</p>
<p>For the lower bound, $1-e^{-u}\geq u/(1+u)$ for $u\geq0$. Under the size-biased law of $X_r$, Jensen's inequality for the convex function $x\mapsto(1+hx)^{-1}$ gives</p>
<div class="math-display">$$G_r(h)\geq\frac{h m_1(r)}{1+h\mathbb E X_r^2/m_1(r)}.$$</div>
<p>Set $r=h^{-1/\kappa}$. The second-moment bound makes the denominator at most $1+C_2$, yielding $G(h)\geq c_1h^\rho/(1+C_2)$.</p>
<p>It remains to pass from transform bounds to tail bounds; no asymptotic Tauberian theorem is needed. Write $q(t)=\mathbb P(T&gt;t)$. The inequality $(1-e^{-1})q(t)\leq G(1/t)$ gives $q(t)\leq C t^{-\rho}$ for large $t$. Enlarge $C$ so that this holds for every $t&gt;0$. Tonelli gives $G(h)=h\int_0^\infty e^{-ht}q(t)\,dt$. For any $a&gt;0$, monotonicity of $q$ therefore gives</p>
<div class="math-display">$$G(h)\leq\frac{C}{1-\rho}a^{1-\rho}h^\rho+e^{-a}q(a/h).$$</div>
<p>Choose $a$ small enough that the first coefficient is less than half the lower coefficient already obtained for $G(h)$. It follows that $q(a/h)\succeq h^\rho$. Since $a$ is fixed, this is the required lower bound for all sufficiently large arguments. Rounding changes no two-sided power bound.</p>
<p>For the long-range scale $\kappa=(d+\alpha)/2$, the exponent is $(d-\alpha)/(d+\alpha)$. The fractional range used in the proof is exactly $\alpha&lt;d$. The additional inequality $d&lt;3\alpha$ belongs to the model-specific derivation of the inputs, not to this analytic transfer.</p>
<p>The <a href="/tag/FJWB/">omitted-edge ghost comparison</a> supplies the comparison hypothesis for a transitive independent-bond model when the omitted-edge row is $O(r^{-\alpha})$ and the retained root cluster is almost surely finite. The <a href="/tag/BEJT/">independent-layer comparison</a> also covers soft intensity cutoffs: <a href="/tag/C4E9/">the power-law row estimate</a> gives the required error bound. Cutoff cluster finiteness remains an explicit prerequisite in both cases.</p>

## A conditional power-law cutoff criterion {#section-power-law-criterion}

<a id="tag-YJ5E" data-assertion="theorem" data-title="Localization and rooted damping give the low-dimensional cutoff-to-tail criterion"></a>
<p>Let $d\geq1$ be an integer, $d/3&lt;\alpha&lt;d$, and $A,\beta&gt;0$. On $\mathbb Z^d$ with Euclidean distance, put $J(x,y)=A|x-y|^{-d-\alpha}$ for $x\ne y$. The full model has independent bond probabilities $1-e^{-\beta J(x,y)}$. For each $r\geq1$, use the soft-cutoff intensities</p>
<div class="math-display">$$\lambda_{xy}(r)=\beta A\bigl(|x-y|^{-d-\alpha}-r^{-d-\alpha}\bigr)_+.$$</div>
<p>Write $K_x^{(r)}$ for a cutoff cluster, $m_q(r)=\mathbb E_r|K_o^{(r)}|^q$, and</p>
<div class="math-display">$$M(r,R)=\min\left\{n\geq1:\mathbb P_r\!\left(\max_x|K_x^{(r)}\cap B_R|\geq n\right)\leq e^{-1}\right\},\qquad M_r=M(r,r).$$</div>
<p>Assume $m_1(r)\asymp r^\alpha$ as $r\to\infty$ and weak cutoff localization of the first four moments. Assume also that fixed constants $A_*,b_*&gt;0$ give the rooted damping estimate</p>
<div class="math-display">$$\mathbb P_r\bigl(|K_o^{(r)}\cap B_R|\geq tM(r,R)\bigr)\leq A_*e^{-b_*t}\mathbb P_r\bigl(|K_o^{(r)}\cap B_R|\geq M(r,R)\bigr)$$</div>
<p>for every $r,R\geq1$ and $t\geq1$. In particular, this damping hypothesis includes windows smaller than the cutoff radius. Let $M_r^*$ be the same window quantile in the full model and put $\kappa=(d+\alpha)/2$. Then</p>
<div class="math-display">$$M_r\asymp M_r^*\asymp r^\kappa,\qquad m_q(r)\asymp r^{\alpha+(q-1)\kappa}\quad(q=1,2,3,4).$$</div>
<p>Moreover $\mathbb E_\beta|K_o\cap B_r|\asymp r^\alpha$, and the cutoff family has mesoscopic negligibility at scale $r^\kappa$. Its full-model root cluster $K_o$ is finite almost surely and satisfies</p>
<div class="math-display">$$\mathbb P_\beta(|K_o|\geq n)\asymp n^{-(d-\alpha)/(d+\alpha)}\qquad(n\to\infty).$$</div>
<p>All comparisons have constants independent of the scale. They are two-sided order bounds, not limiting amplitudes. The theorem does not identify $\beta$ as the critical parameter; an application at criticality must verify these inputs at that parameter.</p>
<p><em>Proof.</em> Couple the cutoff laws by common uniform edge variables. Their clusters and the observation windows increase with $r$, so $M_r$ is nondecreasing and $M(r,Cr)\leq M_{Cr}$ for $C\geq1$. Choose one such $C$ from (wCL) with $\varepsilon=1$. The <a href="/tag/0WAE/">localized damping bounds</a> give, with constants independent of $r$,</p>
<div class="math-display">$$m_2\preceq M_{Cr}m_1,\qquad m_3\preceq M_{Cr}^2m_1,\qquad m_3\preceq M_{Cr}m_2,\qquad m_4\preceq M_{Cr}^2m_2.$$</div>
<p>The fourth moments are finite by (wCL). On each compact radius interval the edge derivatives have bounded finite range, so the countable Russo results apply. Except at the discrete set of lattice distances,</p>
<div class="math-display">$$a(r)=\beta A(d+\alpha)r^{-d-\alpha-1}N_r\sim a_0r^{-\alpha-1},\qquad N_r=\#\{y\ne o:|y|&lt;r\}\asymp r^d,$$</div>
<p>where $a_0=\beta A(d+\alpha)v_d&gt;0$ and $v_d$ is the volume of the Euclidean unit ball. The lattice count follows by comparing the union of unit cubes centered at lattice points with balls whose radii differ by a fixed constant. The <a href="/tag/NJF3/">moment-deficit bounds</a> now supply the two moment equations with errors $e_i(r)\preceq M_{Cr}^2/r^{d+\alpha}$.</p>
<p>The <a href="/tag/LQ6Y/">finite-window quantile bound</a> and $|B_r|\preceq r^d$ give $M_r\preceq r^\kappa$ from the first moment and $m_2(r)\succeq M_r^3/r^d$ from the second. All hypotheses of the <a href="/tag/NS0Q/">all-scale quantile theorem</a> are therefore satisfied. It yields $M_r\asymp r^\kappa$. The displayed moment comparisons give the upper bounds through order four. For the lower bounds, apply the same quantile estimate at order $q$: $m_q(r)\succeq M_r^{q+1}/r^d$, and use $2\kappa-d=\alpha$.</p>
<p>In particular $m_2(r)\asymp r^{\alpha+\kappa}$ and $m_3(r)\preceq r^\kappa m_2(r)$. The <a href="/tag/D7A5/">truncated first-moment inequality</a> and the <a href="/tag/6H7C/">collision bound</a> supply the differential hypotheses of <a href="/tag/KKGL/">the negligibility theorem</a>. Its range $\alpha&lt;\kappa&lt;2\alpha$ is exactly $\alpha&lt;d&lt;3\alpha$. Thus mesoscopic negligibility follows.</p>
<p>Finally, each cutoff cluster is finite almost surely because its mean is finite. The <a href="/tag/C4E9/">omitted-intensity row estimate</a> and <a href="/tag/BEJT/">independent-layer ghost comparison</a> give the comparison used in <a href="/tag/ZWQ3/">the full-tail transfer theorem</a>. The moment bounds and negligibility just proved supply its remaining hypotheses. It gives almost-sure finiteness of the full cluster and the stated exponent $1-\alpha/\kappa=(d-\alpha)/(d+\alpha)$.</p>
<p>It remains to compare the full-model window. Write $Z_r^*=\max_x|K_x\cap B_r|$ and $\rho=(d-\alpha)/(d+\alpha)$. If $Z_r^*\geq n$, at least $n$ vertices of $B_r$ have full-cluster size at least $n$. Transitivity and the full-tail upper bound give</p>
<div class="math-display">$$\mathbb P(Z_r^*\geq n)\leq\frac{|B_r|}{n}\mathbb P(|K_o|\geq n)\preceq r^d n^{-1-\rho}.$$</div>
<p>Since $\kappa(1+\rho)=d$, choosing $n$ a sufficiently large multiple of $r^\kappa$ gives $M_r^*\preceq r^\kappa$. The reverse bound follows by coupling with the cutoff model.</p>
<p>The damping hypothesis passes to the full model at each fixed window radius $R$. Under the increasing coupling, finite paths ensure that all connections between vertices of $B_R$ converge to their full-model values. Hence the window maxima and rooted counts increase to their full-model limits. Their quantiles eventually equal the full quantile: the tail at one less than that quantile is strictly greater than $e^{-1}$, while the cutoff quantiles never exceed it. Pass to the limit in the damping inequality with this eventually fixed integer quantile. This step uses damping for $r&gt;R$, not just $R\geq r$.</p>
<p>Put $M=M_r^*$. For $n\leq M$, the rooted window tail is bounded by the full-volume tail $Cn^{-\rho}$. For $n&gt;M$, the inherited damping bounds it by $C A_* M^{-\rho}e^{-b_*n/M}$. Summing gives</p>
<div class="math-display">$$\mathbb E_\beta|K_o\cap B_r|\preceq M^{1-\rho}\preceq r^\alpha.$$</div>
<p>For the reverse bound, (wCL) at order one gives a fixed $C\geq1$ with $m_1(s)\leq2\mathbb E_s|K_o^{(s)}\cap B_{Cs}|$. Set $s=r/C$ and couple to the full model. For large $r$, this is the required lower bound of order $r^\alpha$.</p>
<p>This criterion leaves three probabilistic inputs visible: cutoff susceptibility of order $r^\alpha$, (wCL), and the uniform rooted damping estimate. It neither proves model-specific localization nor replaces it by a moment-ratio assumption derived from localization itself. The endpoint $\alpha=d$ is outside the fractional-tail conclusion.</p>

## Source scope {#section-source}

<p>S044 of the notes (lines 6068–6200) states mesoscopic negligibility and sketches its use in extracting the full tail. The reciprocal bound above isolates the fixed-truncation step with its quantifiers. The tail theorem supplies an explicit sufficient transfer argument using the earlier ghost comparison, without assuming a limiting size-biased law. The intervening theorem now derives negligibility from the two fixed-truncation differential inequalities and two-sided moment orders, with explicit control of the interval. The first differential inequality is justified above for regular soft cutoffs with finite susceptibility; the collision estimate reduces the second inequality to a uniform third-to-second moment comparison. The final criterion obtains that comparison from (wCL) and rooted damping, while retaining those and the cutoff susceptibility order as explicit model inputs.</p>

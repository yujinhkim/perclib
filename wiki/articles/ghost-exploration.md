---
{
  "id": "ghost-exploration",
  "title": "Exploring the green clusters",
  "subtitle": "Finite ghost algorithms, revealment and covariance",
  "kind": "method",
  "category": "Methods",
  "summary": "Exploring from all green vertices computes ghost connection and bounds edge revealment by endpoint magnetizations. Covariance with an edge-only event reduces to a cluster-size observable.",
  "context": ["A finite nonempty vertex set $V$ and finitely many non-loop bonds $E$.", "Independent bond states, with arbitrary probabilities in $[0,1]$.", "Independent vertex marks $G_v$ of probability $1-e^{-h}$, for finite $h\\geq0$, independent of all bonds."],
  "related": ["exploration", "finite-transcripts", "susceptibility", "russo-formula"],
  "sourceIds": ["notes"],
  "aliases": ["ghost exploration", "green cluster revealment", "ghost covariance", "magnetization algorithm"],
  "prototypeUses": []
}
---

## The exploration and its revealment {#section-algorithm}

<p>Let $K_v$ be the full open cluster of $v$, let $\mathcal G=\{v:G_v=1\}$ and write $B_v=\{K_v\cap\mathcal G\ne\varnothing\}$ and $M_v=\mathbb P(B_v)$. Fix an ordering of the bonds. Reveal all vertex marks and initialize the discovered set $D$ to $\mathcal G$. While an unqueried bond has an endpoint in $D$, query the first such bond; if it is open, add both endpoints to $D$. Stop when no such bond remains.</p>
<a id="tag-XZ7B" data-assertion="proposition" data-title="Finite green-cluster exploration and endpoint revealment bound"></a>
<p>The algorithm terminates after at most $|V|$ mark queries and $|E|$ bond queries. Its final discovered set is $\bigcup_{v\in\mathcal G}K_v$, so membership of a fixed root $o$ in that set computes $B_o$. If $\delta_e$ is the probability that bond $e=\{u,v\}$ is queried, then</p>
<div class="math-display">$$\delta_e\leq\mathbb P(B_u\cup B_v)\leq M_u+M_v.$$</div>
<p>In particular, if all $M_v$ equal $M$, then $\delta_e\leq\min(1,2M)$.</p>
<p><em>Proof.</em> Each query is new, so finiteness gives termination. Every discovered vertex has an open path to an initially green vertex, by induction over discoveries. Conversely, if a green cluster were not completely discovered at termination, an open path from its green vertex to an undiscovered vertex would contain an edge leaving $D$. That edge could not have been queried, since an open query from $D$ discovers its other endpoint; but it would then be an eligible unqueried edge, contradicting termination.</p>
<p>When $e$ is queried, at least one endpoint is already discovered and hence connected to a green vertex in the full configuration. Thus the query event is contained in $B_u\cup B_v$. Taking probabilities and applying the union bound proves the claim. These inclusions are deterministic and do not require independence of the bond states.</p>
<p>The algorithm may reveal more than is needed to decide $B_o$; this does not invalidate its revealment upper bound. Its finite nature does matter. Revealing every mark first on an infinite graph is not a finite initial segment of a sequential decision tree. An infinite-volume application needs a separate construction or a limiting argument.</p>

## Covariance with a bond event {#section-covariance}

<a id="tag-6X74" data-assertion="proposition" data-title="Ghost covariance identity for bond-measurable events"></a>
<p>Let $A$ be any event depending only on the bond states and put $T=|K_o|$. Then</p>
<div class="math-display">$$\operatorname{Cov}(\mathbf1_A,\mathbf1_{B_o})=\operatorname{Cov}_{\rm bonds}(\mathbf1_A,1-e^{-hT}).$$</div>
<p>For every vertex $v$, $\operatorname{Cov}(\mathbf1_A,G_v)=0$. In particular, if $A_n=\{T\geq n\}$ with integer $n\geq1$, then</p>
<div class="math-display">$$\operatorname{Cov}(\mathbf1_{A_n},\mathbf1_{B_o})\geq\mathbb P(A_n)\bigl(1-e^{-hn}-M_o\bigr).$$</div>
<p><em>Proof.</em> Conditional on the complete bond configuration, the cluster is fixed and all its marks remain independent. The conditional probability of avoiding every green vertex is $(e^{-h})^T$, so</p>
<div class="math-display">$$\mathbb E[\mathbf1_{B_o}\mid\text{bonds}]=1-e^{-hT}.$$</div>
<p>Multiply by the bond-measurable indicator of $A$ and take expectations, then subtract $\mathbb P(A)M_o$. This proves the covariance identity. Independence of $A$ and each $G_v$ proves the zero-covariance assertion. Finally, on $A_n$ one has $1-e^{-hT}\geq1-e^{-hn}$; inserting this into the joint expectation gives the last inequality. It remains valid when $\mathbb P(A_n)=0$, without a conditional probability given that event.</p>
<p>The last lower bound need not be positive. To obtain a useful positive covariance estimate from it, one must also control $M_o$ relative to $1-e^{-hn}$. The formula alone does not provide that control.</p>

## Which ghost covariances vanish {#section-scope}

<p>The zero-covariance statement applies to the bond-only event $A$, not to $B_o$. On a graph with one vertex and no bonds, $B_o=\{G_o=1\}$, so for $h&gt;0$</p>
<div class="math-display">$$\operatorname{Cov}(\mathbf1_{B_o},G_o)=(1-e^{-h})e^{-h}&gt;0.$$</div>
<p>Thus revealing all marks is harmless in a covariance inequality whose first observable is bond-measurable only because its mark covariances vanish. The same deletion of terms is not justified when that first observable is the ghost-connection event itself.</p>
<p>The article supplies the finite exploration and covariance calculations used in the preliminary notes, Chapter 6, lines 2645–2672 and 2792–2802. The latter passage's discussion of disappearing ghost terms must be read with the distinction above; the source audit already flags this issue. The following derivative theorem adds the finite covariance inequality and the regularity argument needed for infinite volume; it does not use an infinite all-marks-first decision tree.</p>

## A cluster-tail differential inequality {#section-tail-derivative}

<a id="tag-JM30" data-assertion="theorem" data-title="Countable cluster-tail derivative bound from finite ghost exploration"></a>
<p>Consider independent bonds on a nonempty countable vertex set, with probabilities $1-e^{-\beta J_e}$ and finite nonnegative weights satisfying $\sum_{e\ni v}J_e\leq W&lt;\infty$ at every vertex. For an integer $n\geq1$, put</p>
<div class="math-display">$$p_n(v,\beta)=\mathbb P_\beta(|K_v|\geq n),\qquad m_n^*(\beta)=\sup_v\mathbb E_\beta[|K_v|\wedge n],\qquad c_0=1-e^{-1}.$$</div>
<p>Each $p_n(v,\cdot)$ is locally Lipschitz on $(0,\infty)$, with $0\leq p_n'\leq Wn$ almost everywhere, and</p>
<div class="math-display">$$p_n'(v,\beta)\geq\frac1{2\beta}\left(\frac{c_0n}{m_n^*(\beta)}-1\right)p_n(v,\beta)\quad\text{for almost every }\beta&gt;0.$$</div>
<p>In a transitive model $m_n^*(\beta)=\mathbb E_\beta[|K_o|\wedge n]$. No logarithm of a zero event probability is required.</p>
<p><em>Proof.</em> First work in a finite vertex set $F$ with its induced bonds, fixing $h&gt;0$. Apply the <a href="#/entropy-comparison">finite covariance inequality</a> with the tree computing $B_o$, $f=\mathbf1_{B_o}$, and the increasing bond event $g=\mathbf1_{\{|K_o^F|\geq n\}}$. Mark covariances vanish because $g$ is bond-measurable. With $M_F^*=\max_{v\in F}M_v$, the revealment and covariance bounds above give</p>
<div class="math-display">$$p_n^F(o,\beta)(1-e^{-hn}-M_F^*)\leq 2M_F^*\sum_e\operatorname{Cov}(g,\omega_e).$$</div>
<p>For $J_e&gt;0$, finite-coordinate Russo and conditioning on that bit give</p>
<div class="math-display">$$\frac{d}{d\beta}p_n^F(o,\beta)=\sum_{e:J_e&gt;0}\frac{J_e}{1-e^{-\beta J_e}}\operatorname{Cov}(g,\omega_e)\geq\frac1\beta\sum_e\operatorname{Cov}(g,\omega_e).$$</div>
<p>Coordinates of weight zero have zero covariance. Now take $h=1/n$. The bound $1-e^{-t/n}\leq\min(t/n,1)$ and inclusion in the full cluster give $0&lt;M_F^*\leq m_n^*(\beta)/n$. Substitution yields</p>
<div class="math-display">$$(p_n^F)'\geq\frac1{2\beta}\left(\frac{c_0}{M_F^*}-1\right)p_n^F\geq\frac1{2\beta}\left(\frac{c_0n}{m_n^*(\beta)}-1\right)p_n^F.$$</div>
<p>These inequalities remain valid when their right sides are negative.</p>
<p>For the limit, first obtain a uniform derivative upper bound. A pivotal coordinate must be queried by any tree computing the event: otherwise changing it would leave the transcript and output unchanged. Finite Russo and the <a href="#/stopped-exploration">stopped exploration cost</a> thus give $0\leq(p_n^F)'\leq\sum_eJ_e\delta_e\leq Wn$. Exhausting the vertex set, finite path witnesses give $p_n^F(v,\beta)\uparrow p_n(v,\beta)$. Passing to the limit in the Lipschitz estimate proves the asserted regularity, uniformly in $v$.</p>
<p>Since $\mathbb E[|K_v|\wedge n]=\sum_{k=1}^n p_k(v,\beta)$, these expectations have a common Lipschitz bound; their supremum $m_n^*$ does too. In particular the function</p>
<div class="math-display">$$L(\beta)=\frac1{2\beta}\left(\frac{c_0n}{m_n^*(\beta)}-1\right)$$</div>
<p>is continuous on $(0,\infty)$, since $1\leq m_n^*\leq n$. On any compact parameter interval the finite-volume inequality makes $\exp(-\int L)\,p_n^F$ nondecreasing. Its pointwise limit has the same property. The already-established Lipschitz regularity then implies $p_n'\geq Lp_n$ almost everywhere, completing the proof.</p>
<p>This supplies the tail differential bound in the notes' S016, lines 2561–2581, using the finite ghost algorithm. On a compact positive parameter interval it has the stated form $p_n'\geq(cn/m_n^*-C)p_n$ with explicit constants. The infinite passage does not start by revealing every mark on an infinite graph.</p>

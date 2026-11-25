---
{
  "id": "site-percolation",
  "title": "Site percolation",
  "subtitle": "Open vertices, empty closed-root clusters, and association",
  "kind": "model",
  "category": "Models",
  "summary": "Site percolation retains vertices independently. Its self-connection probability is the root's open probability, and its cluster is empty when the root is closed.",
  "context": ["A fixed simple graph $G=(V,E)$ and a set $\\omega\\subseteq V$ of open vertices.", "Under $\\mathbb P_w$, vertex $v$ is open independently with probability $w_v\\in[0,1]$.", "Countability of $V$ is imposed for the measurable-event and probability statements below, not for deterministic definitions."],
  "related": ["product-model", "connectivity", "harris-inequality", "criticality"],
  "sourceIds": ["perclib-site-interface", "perclib-site-harris"],
  "aliases": ["site model", "open vertices", "site cluster", "site critical probability"],
  "prototypeUses": []
}
---

## Open-vertex connections {#section-definition}

<a id="tag-8FLS" data-assertion="definition" data-title="Site connections and the closed-root convention"></a><p>Write $x\leftrightarrow_{\mathrm s}y$ if there is a finite path in $G$ from $x$ to $y$ whose every vertex is open, including both endpoints. Define $K_{\mathrm s}(x)=\{y:x\leftrightarrow_{\mathrm s}y\}$. The length-zero path is allowed only when $x$ is open. Thus $K_{\mathrm s}(x)=\varnothing$ when $x$ is closed, while an open $x$ belongs to its own cluster.</p><p>Equivalently, retain a graph edge precisely when both endpoints are open, and require the starting vertex to be open before using reachability in that graph. The extra requirement matters: ordinary graph reachability makes every isolated vertex reachable from itself, including a closed vertex. Site clusters partition the open vertices; they do not give a partition of all vertices into nonempty clusters.</p>

<p>These definitions work on any vertex set. Reversing or concatenating open paths proves symmetry and transitivity of site connection. Consequently, connected open roots have the same cluster. If $\omega\subseteq\eta$, every edge retained by $\omega$ is retained by $\eta$, and every site cluster can only grow. Connection to a fixed set $A\subseteq V$ means connection to at least one of its vertices, so this event is increasing as well. An infinite site cluster stays infinite after vertices are opened.</p>

## Basic probabilities {#section-probabilities}

<a id="tag-9R9K" data-assertion="proposition" data-title="Self-connection and adjacent-site connection probabilities"></a><p>Let $\tau_{\mathrm s}(x,y)=\mathbb P_w(x\leftrightarrow_{\mathrm s}y)$. Then</p><div class="math-display">$$\tau_{\mathrm s}(x,x)=w_x,\qquad \tau_{\mathrm s}(x,y)\leq w_xw_y\quad(x\neq y).$$</div><p>If $\{x,y\}$ is an edge of $G$, equality holds in the second formula.</p><p><em>Proof.</em> Self-connection is exactly the event that $x$ is open. A connection between distinct endpoints requires both to be open, whose joint probability is $w_xw_y$ by independence. For adjacent vertices, their common openness also suffices, using the one-edge path.</p><p>In particular, these probabilities differ from bond percolation even on a two-vertex graph. At a homogeneous parameter $p$, the site connection probability is $p^2$, while the bond connection probability is $p$. The bond root also has self-connection probability one.</p>

## Measurability and association {#section-association}

<a id="tag-3YMY" data-assertion="proposition" data-title="Site connection and infinite-cluster events are measurable and increasing"></a><p>On a countable vertex set, each event $\{x\leftrightarrow_{\mathrm s}y\}$ and $\{|K_{\mathrm s}(x)|=\infty\}$ is measurable and increasing in the open-vertex configuration. For any increasing finite exhaustion $F_n\uparrow V$,</p><div class="math-display">$$\{|K_{\mathrm s}(x)|=\infty\}=\bigcap_n\bigcup_{y\notin F_n}\{x\leftrightarrow_{\mathrm s}y\}.$$</div><p><em>Proof.</em> A connection is a countable union of cylinder events, one for each finite path, requiring its vertices to be open. A cluster is infinite precisely when it is not contained in any member of the exhaustion, giving the displayed countable intersection of countable unions. Opening more vertices preserves every open path and can only enlarge the cluster.</p>

<p>The finite-witness description itself needs no countability: a connection is the union over finite vertex lists starting at $x$ and ending at $y$ of the event that the list is an open walk and its starting vertex is open. For any fixed list, its open-walk event is a finite intersection of vertex cylinders, hence measurable in any ambient vertex set. Similarly, a cluster is infinite exactly when it connects to the complement of every finite subset of $V$. Countability is used to turn these unions and intersections into measurable events; it is not needed for the underlying set identities.</p>

<a id="tag-AR5B" data-assertion="proposition" data-title="Site Harris bounds and transfer of an infinite cluster"></a><p>For any two site-connection events, or any two rooted infinite-site-cluster events, their joint probability is at least the product of their probabilities. In particular, writing $\theta_{\mathrm s}(x)=\mathbb P_w(|K_{\mathrm s}(x)|=\infty)$,</p><div class="math-display">$$\tau_{\mathrm s}(x,y)\tau_{\mathrm s}(y,z)\leq\tau_{\mathrm s}(x,z),\qquad \tau_{\mathrm s}(x,y)\theta_{\mathrm s}(x)\leq\theta_{\mathrm s}(y).$$</div><p><em>Proof.</em> Apply the <a href="/tag/X5SS/">Harris inequality</a> to the measurable increasing events just described, now with vertices as the independent coordinates. Two successive site connections imply the connection between their outer endpoints. A connection from $x$ to $y$ also makes their open clusters equal, so an infinite cluster at $x$ is then infinite at $y$. These event containments give the two bounds.</p>

## The lattice threshold convention {#section-threshold}

<a id="tag-8EIH" data-assertion="definition" data-title="Site critical probability on the nearest-neighbour lattice"></a><p>For homogeneous site percolation on the nearest-neighbour graph of $\mathbb Z^d$, $d\geq0$, let</p><div class="math-display">$$\theta_{\mathrm s}(p)=\mathbb P_p(|K_{\mathrm s}(0)|=\infty),\qquad p_{\mathrm c}^{\mathrm s}=\inf\bigl(\{p\in[0,1]:\theta_{\mathrm s}(p)&gt;0\}\cup\{1\}\bigr).$$</div><p>The extra element $1$ makes the set nonempty and places this real-valued threshold in $[0,1]$, even if no parameter percolates. For $d=0$, the graph is a singleton, so $\theta_{\mathrm s}(p)=0$ for every $p$ and this convention gives $p_{\mathrm c}^{\mathrm s}=1$.</p><p>This definition alone says nothing about $\theta_{\mathrm s}(p_{\mathrm c}^{\mathrm s})$. It is also distinct from an extended-valued bond-intensity threshold, which may be infinite.</p>

## Ordered profiles and the threshold {#section-monotonicity}

<a id="tag-M28D" data-assertion="proposition" data-title="Site profile comparison and the two sides of the capped threshold"></a>
<p>On a countable vertex set, let $w_v\leq w'_v$ for every vertex. For every measurable event $A$ increasing in the set of open vertices,</p>
<div class="math-display">$$\mathbb P_w(A)\leq\mathbb P_{w'}(A).$$</div>
<p>In particular, the homogeneous infinite-cluster probability at any root of a fixed graph is nondecreasing in $p$. For the nearest-neighbour lattice threshold defined above and $p\in[0,1]$,</p>
<div class="math-display">$$p&lt;p_{\mathrm c}^{\mathrm s}\ \Longrightarrow\ \theta_{\mathrm s}(p)=0,
\qquad p&gt;p_{\mathrm c}^{\mathrm s}\ \Longrightarrow\ \theta_{\mathrm s}(p)&gt;0.$$</div>
<p><em>Proof.</em> The <a href="/tag/6B9V/">ordered-profile coupling</a>, applied to vertex coordinates, makes the $w$-configuration a subset of the $w'$-configuration almost surely. Increasingness gives the probability comparison. Apply it to the measurable infinite-cluster event for monotonicity.</p>
<p>If $p&lt;p_{\mathrm c}^{\mathrm s}$ and $\theta_{\mathrm s}(p)&gt;0$, then $p$ belongs to the set defining the infimum, a contradiction. Conversely, if $p&gt;p_{\mathrm c}^{\mathrm s}$, the defining set has an element $r&lt;p$. This element cannot be supplied solely by the adjoined endpoint $1$, since $p\leq1$. Hence $\theta_{\mathrm s}(r)&gt;0$, and monotonicity gives $\theta_{\mathrm s}(p)\geq\theta_{\mathrm s}(r)&gt;0$.</p>
<p>No conclusion at $p=p_{\mathrm c}^{\mathrm s}$ follows. On the singleton lattice ($d=0$), the threshold is one and the above-threshold implication has no parameter in $[0,1]$ to which it applies. At the zero profile, every connection probability is zero, including self-connection. On a two-vertex edge at $p=1/2$, the supermultiplicative inequality can be strict: $\tau_{\mathrm s}(x,y)\tau_{\mathrm s}(y,x)=1/16&lt;1/2=\tau_{\mathrm s}(x,x)$.</p>

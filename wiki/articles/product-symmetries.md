---
{
  "id": "product-symmetries",
  "title": "Relabelling product percolation",
  "subtitle": "Transport the profile along with the coordinates",
  "kind": "method",
  "category": "Foundations",
  "summary": "A bijection of coordinates transports a Bernoulli product law by composing its profile with the inverse bijection. Symmetry requires preservation of that profile.",
  "context": ["Arbitrary coordinate sets $I,K$ and a bijection $e:I\\to K$.", "Product sigma-algebras and profiles $q:I\\to[0,1]$.", "For bond applications, vertex relabelling induces relabelling of unordered pairs."],
  "related": ["product-model", "connectivity", "susceptibility", "finite-random-graphs"],
  "sourceIds": ["mathlib", "perclib-diagonal", "perclib-reindexing", "perclib-host-support"],
  "aliases": ["reindexing", "permutation", "symmetry", "invariant law", "relabelling"],
  "prototypeUses": []
}
---

## Transporting the law {#section-transport}

<p>Identify a configuration with its set of open coordinates. A bijection $e:I\to K$ induces $R_e(\omega)=e[\omega]$. The value at $k$ after relabelling is the old value at $e^{-1}(k)$, so the transported profile must be $q\circ e^{-1}$.</p>

<a id="tag-6RZ8" data-assertion="proposition" data-title="Product-law transport under coordinate bijections"></a><p>The map $R_e$ is a measurable bijection with measurable inverse, and</p><div class="math-display">$$(R_e)_*\mathbb P_q=\mathbb P_{q\circ e^{-1}}.$$</div><p>Equivalently, for every measurable event $A$ on $K$,</p><div class="math-display">$$\mathbb P_q(R_e^{-1}(A))=\mathbb P_{q\circ e^{-1}}(A).$$</div><p><em>Proof.</em> The inverse image under $R_e$ of the event that $k$ is open is the event that $e^{-1}(k)$ is open. Coordinate events generate the product sigma-algebra, so $R_e$ is measurable; applying the same argument to $e^{-1}$ gives its measurable inverse. A finite cylinder on $K$ pulls back to the corresponding cylinder on distinct coordinates of $I$. Its probability is the product of the Bernoulli weights with parameters $q(e^{-1}(k))$. Thus the pushforward and the stated product law agree on the cylinder pi-system. Uniqueness of probability measures on its generated sigma-algebra proves the identity.</p><p>No countability assumption is needed. Parameters zero and one cause no exception, since the cylinder argument uses no division.</p>

## When relabelling is a symmetry {#section-invariance}

<a id="tag-VEUZ" data-assertion="corollary" data-title="Profile-preserving permutations preserve the product law"></a><p>If $e:I\to I$ is a bijection satisfying $q(e(i))=q(i)$ for every $i$, then $(R_e)_*\mathbb P_q=\mathbb P_q$. Hence $\mathbb P_q(R_e^{-1}(A))=\mathbb P_q(A)$ for every measurable event $A$.</p><p><em>Proof.</em> Apply the profile equality at $e^{-1}(i)$ to obtain $q(e^{-1}(i))=q(i)$, and use the transport identity.</p><p>A homogeneous profile is preserved by every permutation of its coordinates. For an inhomogeneous profile, a permutation generally changes the law. In particular, if two coordinates have different opening probabilities, exchanging them exchanges those marginal probabilities. The combinatorial symmetry of an index set alone is not a symmetry of its probability law.</p>

## Unordered pairs and diagonal coordinates {#section-bonds}

<a id="tag-6VY0" data-assertion="corollary" data-title="Transport of a bond profile by vertex relabelling"></a><p>Let $f:V\to W$ be a bijection and let $f_2$ be its induced bijection of unordered pairs, including repeated pairs: $f_2(\{x,y\})=\{f(x),f(y)\}$. If bonds have profile $q$, relabelling their open set by $f_2$ gives product profile</p><div class="math-display">$$q'(\{u,v\})=q(\{f^{-1}(u),f^{-1}(v)\}).$$</div><p>This is the coordinate-transport proposition applied to $f_2$.</p><p>The simple open graph discards repeated pairs $\{x,x\}$, but the underlying product configuration retains those coordinates. To claim invariance of the <em>entire product law</em> under a vertex permutation, profile preservation is required on all coordinates, including repeated pairs. Arbitrary diagonal values are allowed; they need not be zero. Statements about only the simple open graph may ignore the diagonal, but that is a distinct claim.</p><p>For example, on two vertices with unequal diagonal opening probabilities, swapping the vertices changes the full product law. Its only non-loop edge is fixed by the swap, so the simple open graph nevertheless has the same law. This separates invariance of graph observables from invariance of all coordinate events.</p>

## Erasing loops {#section-erasure}

<a id="tag-LNKT" data-assertion="theorem" data-title="Loop erasure transports the product law and preserves insensitive observables"></a>
<p>Let $V$ be any vertex set, let $D=\{\{v,v\}:v\in V\}$ be the diagonal coordinates, and put $E(\omega)=\omega\setminus D$. For a profile $p$ on unordered pairs, define $p^\circ(e)=0$ on $D$ and $p^\circ(e)=p(e)$ elsewhere. Then $E$ is measurable and</p>
<div class="math-display">$$E_*\mathbb P_p=\mathbb P_{p^\circ}.$$</div>
<p>If profiles $p,q$ agree off $D$, and $F$ is a measurable map to any measurable space satisfying $F(E(\omega))=F(\omega)$ for every configuration, then</p>
<div class="math-display">$$F_*\mathbb P_p=F_*\mathbb P_q.$$</div>
<p>In particular, every measurable event unchanged by loop erasure has the same probability under these two profiles. Countability of $V$ is not required.</p>
<p><em>Proof.</em> Each output coordinate of $E$ is either constantly closed or equal to its input coordinate. This proves measurability, and the probabilities of finite output cylinders are exactly those of the product profile $p^\circ$. Cylinder uniqueness gives the first identity. Since $p^\circ=q^\circ$, composition of pushforwards gives</p>
<div class="math-display">$$F_*\mathbb P_p=(F\circ E)_*\mathbb P_p=F_*\mathbb P_{p^\circ}=F_*\mathbb P_{q^\circ}=(F\circ E)_*\mathbb P_q=F_*\mathbb P_q.$$</div>
<p>Apply this to an event's indicator for the last claim. The argument includes diagonal probabilities zero and one; it does not condition on a possibly null event that all loops are closed.</p>

<a id="tag-EYCQ" data-assertion="corollary" data-title="Diagonal parameters do not affect connection probabilities or cluster-volume laws"></a>
<p>Suppose $V$ is countable and $p,q$ agree on every pair of distinct vertices. Let $K_x$ be the cluster of $x$ in the simple open graph, with the length-zero path allowed. Then for all $x,y\in V$,</p>
<div class="math-display">$$\mathbb P_p(x\leftrightarrow y)=\mathbb P_q(x\leftrightarrow y),\qquad \mathcal L_p(|K_x|)=\mathcal L_q(|K_x|),\qquad \chi_p(x)=\chi_q(x).$$</div>
<p>The volume law takes values in $\mathbb N\cup\{\infty\}$, and susceptibility is an extended nonnegative expectation. Thus all cluster-volume tail probabilities and all nonnegative moments agree, whether finite or infinite.</p>
<p><em>Proof.</em> Deleting repeated pairs leaves the simple open graph unchanged, hence leaves connectivity and each root cluster unchanged. On a countable vertex set, connectivity is a countable union of finite-path cylinder events. Also $|K_x|=\sum_{y\in V}\mathbf1_{\{x\leftrightarrow y\}}$ is measurable as a monotone limit of finite sums. Apply the preceding theorem to these observables, and integrate any nonnegative function of the volume against the common law. No finiteness assumption on susceptibility enters.</p>
<p>These conclusions concern graph observables. The event that a specified loop is open still has probability equal to that loop's parameter, and can distinguish $\mathbb P_p$ from $\mathbb P_q$.</p>

<p>On two vertices, replacing both loop parameters by zero or by one leaves the susceptibility unchanged for every off-diagonal probability. The equality also reaches genuinely infinite values: on a countably infinite vertex set with every off-diagonal probability one, every such pair is open simultaneously almost surely, so the graph is complete and each susceptibility is infinite. Choosing zero instead of one on the diagonal changes none of this.</p>

## Host support and diagonal coordinates {#section-host}

<a id="tag-H48I" data-assertion="proposition" data-title="Host containment for configurations and for their simple graphs"></a>
<p>Let $V$ be countable, let $G$ be a simple graph on $V$, and let $\mathbb P_q$ be the product law on all unordered pairs, including diagonal pairs. Then</p>
<div class="math-display">$$\mathbb P_q(\omega\subseteq E(G))=1\quad\Longleftrightarrow\quad q(e)=0\text{ for every }e\notin E(G).$$</div>
<p>In contrast, writing $G_\omega$ for the simple open graph,</p>
<div class="math-display">$$\mathbb P_q(G_\omega\subseteq G)=1\quad\Longleftrightarrow\quad q(\{x,y\})=0\text{ whenever }x\ne y\text{ and }\{x,y\}\notin E(G).$$</div>
<p>The first condition forces every diagonal probability to be zero, since a simple host has no loops. The second places no restriction on diagonal probabilities. No degree bound on $G$ is assumed.</p>
<p><em>Proof.</em> An outside coordinate $e$ is open with probability $q(e)$. If all these probabilities vanish, the union of the outside-open events is a countable union of null events, since the unordered-pair set of a countable vertex set is countable. Its complement is exactly configuration containment. Conversely, any outside-open event is contained in the failure of configuration containment, so almost-sure containment forces its marginal to be zero.</p>
<p>For graph containment the same argument uses only non-diagonal pairs outside the host. An open such pair is an edge of the simple open graph and violates containment, while diagonal coordinates never contribute an edge. These countable unions also establish measurability of both containment events.</p>
<p>For example, on a nonempty countable vertex set, give every diagonal probability one and every other probability zero. The simple open graph is empty almost surely and lies in every host, but the configuration does not lie in the edge set of any simple host. On the other hand, arbitrary probabilities on host edges, including one, are allowed in both criteria once the required outside probabilities vanish.</p>
<p>The library's host interface assumes the stronger all-pair support condition and obtains both containments together. The graph-only criterion and the converse directions above make the distinction explicit; they are additional expository consequences of the coordinate marginals.</p>

---
{
  "id": "cluster-partitions",
  "title": "Cluster partitions and root averages",
  "subtitle": "Counting components once or once per vertex",
  "kind": "method",
  "category": "Foundations",
  "summary": "Clusters partition the vertices. Grouping root sums by components explains squared cluster sizes, size-biased sampling, and deterministic comparisons with the largest cluster in a window.",
  "context": ["A fixed open configuration on a vertex set $V$; no probability law is needed for the partition identities.", "$K(x)$ is the cluster containing $x$, including $x$ itself.", "Finite sets are explicitly required for finite sums and uniform sampling."],
  "related": ["connectivity", "susceptibility", "universal-tightness", "finite-random-graphs"],
  "sourceIds": ["perclib-bond-interface", "perclib-susceptibility-interface", "perclib-cluster-partition"],
  "aliases": ["cluster partition", "connected components", "root average", "component moments", "size biased sampling"],
  "prototypeUses": []
}
---

## Open pairs and the simple graph {#section-open-pairs}

<a id="tag-Q0D1" data-assertion="proposition" data-title="Open-graph monotonicity and the singleton-cluster convention"></a>
<p>Let $V$ be any vertex set and let $\omega$ be a set of unordered pairs, with repeated pairs allowed as coordinates. The associated simple graph joins $x$ and $y$ exactly when $x\ne y$ and $\{x,y\}\in\omega$. If $\omega\subseteq\omega'$, then every connection in $\omega$ is a connection in $\omega'$, and</p>
<div class="math-display">$$K_\omega(x)\subseteq K_{\omega'}(x).$$</div>
<p>Every cluster contains its root and therefore has extended volume at least one. If no pair of distinct vertices is open, then $K_\omega(x)=\{x\}$ for every $x$, whatever the diagonal coordinates. Conversely, one open pair of distinct vertices connects its endpoints. These statements require neither countability nor a probability law.</p>
<p><em>Proof.</em> Inclusion of configurations preserves every adjacency and hence every finite open path. The length-zero path puts $x$ in its own cluster. With no open pair of distinct vertices, no path of positive length can take even its first step, so the only reachable vertex is $x$. An open pair with distinct endpoints supplies a path of length one.</p>
<p>In particular, on two distinct vertices the all-closed configuration disconnects them and the configuration containing their pair connects them. The empty configuration has singleton clusters, not empty clusters. For a probability law on a countable vertex set, reflexivity and symmetry of connection give $\tau(x,x)=1$, $\tau(x,y)=\tau(y,x)$ and $0\leq\tau(x,y)\leq1$. Full configuration laws can still distinguish diagonal parameters; only the simple graph ignores them.</p>

## Components as classes {#section-partition}

<a id="tag-0N0J" data-assertion="proposition" data-title="Root clusters form a partition"></a><p>For any vertices $x,y$,</p><div class="math-display">$$K(x)=K(y)\quad\Longleftrightarrow\quad x\leftrightarrow y.$$</div><p>Any two root clusters are therefore either equal or disjoint, and the distinct clusters partition $V$. No countability, local finiteness or independence hypothesis is required.</p><p><em>Proof.</em> Connectivity by finite paths is an equivalence relation: the empty path gives reflexivity, reversing a path gives symmetry, and concatenation gives transitivity. Its equivalence class at $x$ is exactly $K(x)$. Equivalence classes are equal precisely when their representatives are equivalent, and otherwise are disjoint.</p>

## Grouping a sum by components {#section-sums}

<a id="tag-TUD2" data-assertion="theorem" data-title="Finite root sums equal size-weighted component sums"></a><p>Suppose $V$ is finite, and let $\mathcal C$ be its set of distinct open components. For every function $f:\mathbb N\to\mathbb R$,</p><div class="math-display">$$\sum_{x\in V}f(|K(x)|)=\sum_{C\in\mathcal C}|C|f(|C|).$$</div><p>In particular,</p><div class="math-display">$$\sum_{x\in V}|K(x)|=\sum_{C\in\mathcal C}|C|^2.$$</div><p>The same identities apply to the graph induced on a finite vertex domain, with its internal components and internal clusters.</p><p><em>Proof.</em> Partition the sum on the left according to the component containing $x$. On a component $C$, every summand equals $f(|C|)$, and there are $|C|$ such summands. Taking $f(n)=n$ gives the squared-size formula. Apply the same argument to the induced graph for the domain version. If $V$ is empty, both sums are empty and equal zero.</p>

## Choosing a root {#section-sampling}

<p>The <a href="/tag/CY0D/">uniform-root component formula</a> gives the following sampling interpretation. Fix a configuration on a finite nonempty $V$, and choose a vertex $U$ uniformly from $V$. For each distinct component $C$,</p><div class="math-display">$$\mathbb P(K(U)=C\mid\omega)=\frac{|C|}{|V|},\qquad \mathbb E[|K(U)|\mid\omega]=\frac1{|V|}\sum_{C\in\mathcal C}|C|^2.$$</div><p>If instead a component is chosen uniformly from $\mathcal C$, its mean size is $|V|/|\mathcal C|$. The uniform-root component law is the size bias of this uniform-component law.</p><p><em>Proof.</em> Exactly the vertices of $C$ select $C$, giving the first probability. Summing its product with $|C|$ gives the expectation. Under uniform-component sampling, the mean size is $\sum_C|C|/|\mathcal C|=|V|/|\mathcal C|$. Biasing its mass $1/|\mathcal C|$ by $|C|$ and normalizing by this mean gives $|C|/|V|$.</p><p>For a random configuration and an independent uniform root, taking another expectation gives the existing <a href="/tag/XCGS/">averaged susceptibility identity</a></p><div class="math-display">$$\frac1{|V|}\sum_{x\in V}\mathbb E|K(x)|=\frac1{|V|}\mathbb E\!\left[\sum_{C\in\mathcal C}|C|^2\right].$$</div><p>No transitivity is needed for this averaged identity. Replacing the average over roots by one fixed root requires additional symmetry.</p>

## Observing clusters in a window {#section-window}

<a id="tag-RU6O" data-assertion="proposition" data-title="Window intersection moments and the largest observed cluster"></a><p>Let $\Lambda\subseteq V$ be finite and nonempty, with $V$ otherwise arbitrary. Form the finite partition</p><div class="math-display">$$\mathcal C_\Lambda=\{C\cap\Lambda:C\text{ is a full open component and }C\cap\Lambda\neq\varnothing\},$$</div><p>and let $M_\Lambda=\max_{D\in\mathcal C_\Lambda}|D|$. Then</p><div class="math-display">$$\sum_{x\in\Lambda}|K(x)\cap\Lambda|=\sum_{D\in\mathcal C_\Lambda}|D|^2,\qquad M_\Lambda^2\leq\sum_{x\in\Lambda}|K(x)\cap\Lambda|\leq M_\Lambda|\Lambda|.$$</div><p><em>Proof.</em> Intersecting the full component partition with $\Lambda$ and discarding empty intersections gives a partition of $\Lambda$. Grouping the root sum by these classes proves the identity. One class has size $M_\Lambda$, so its square gives the lower bound. For the upper bound, use $|D|^2\leq M_\Lambda|D|$ and $\sum_D|D|=|\Lambda|$.</p><p>These classes need not be the components of the induced graph on $\Lambda$: two observed vertices may be joined by an excursion outside the window. For an open path $x-z-y$ with $\Lambda=\{x,y\}$ and $z\notin\Lambda$, the full-cluster intersection is one class of size two, whereas the induced graph has two singleton components. The corresponding squared-size sums are four and two. This is the observation-window convention used by <a href="#/universal-tightness">maximum-cluster tightness</a>.</p>

## The cluster as a measurable random set {#section-random-set}

<a id="tag-GUHT" data-assertion="proposition" data-title="Cluster-set measurability and the extended connection-indicator sum"></a>
<p>On a countable vertex set, the map $\omega\mapsto K_\omega(x)$ is measurable from the bond configuration space to $2^V$, with the product sigma-algebra on each. Its extended volume $|K_\omega(x)|\in\mathbb N\cup\{\infty\}$ is measurable as well. The deterministic identity</p>
<div class="math-display">$$|K_\omega(x)|=\sum_{y\in V}\mathbf1_{\{x\leftrightarrow y\}}(\omega)$$</div>
<p>holds on an arbitrary vertex set, interpreting the nonnegative sum as the supremum of its finite subsums and every infinite cardinality as $\infty$.</p>
<p><em>Proof.</em> Membership at $y$ is a generating coordinate event of $2^V$, and its inverse image under the cluster map is the connection event $\{x\leftrightarrow y\}$. On a countable vertex set this is measurable by the finite-path argument, proving measurability of the random set.</p>
<p>For the identity, a finite cluster contributes exactly one for each of its vertices. An infinite cluster contains finite subsets of arbitrarily large size, so the supremum of finite subsums is infinite. When $V$ is countable, enumerate it by increasing finite sets. The corresponding indicator sums are measurable and increase to the extended volume. Equivalently, each volume threshold is a countable union of measurable finite-sum thresholds, proving measurability as an extended integer-valued variable.</p>
<p>Integrating the nonnegative sum gives the <a href="/tag/8DSI/">susceptibility identity</a> by Tonelli, including infinite values. This step requires measurable connection events; the arbitrary-set deterministic identity alone supplies no such measurability. The empty configuration contributes the root term one.</p>

<p>The measurability argument also separates finite witnesses from countability. For any finite vertex list, the event that consecutive vertices form an open walk is a finite intersection of coordinate cylinders (or the empty event if two consecutive vertices coincide), so it is measurable for arbitrary $V$. Connection is the union over lists with the specified endpoints. An infinite cluster is equivalently one that connects to the complement of every finite subset of $V$. These are set identities without countability; countability makes the relevant unions and intersections countable and hence measurable. Neither graph definitions nor deterministic root-cluster identities require measurable connection events.</p>

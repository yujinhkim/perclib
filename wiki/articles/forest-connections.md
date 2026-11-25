---
{
  "id": "forest-connections",
  "title": "Percolation on a forest",
  "subtitle": "Exact path weights and the ray",
  "kind": "model",
  "category": "Models",
  "summary": "Unique paths turn connection probabilities into finite products and susceptibility into an exact sum of path weights. The ray gives formulas at every parameter, including both endpoints.",
  "context": ["Independent bond percolation on a countable vertex set $V$, with probabilities $q_e\\in[0,1]$.", "A deterministic simple graph $G$ contains the open graph almost surely and is acyclic.", "Diagonal bond probabilities are unrestricted and do not affect the open graph."],
  "related": ["connectivity", "susceptibility", "subcritical-bound", "binary-tree-percolation"],
  "sourceIds": ["perclib-forest-interface"],
  "aliases": ["forest", "acyclic", "unique path", "ray", "geometric susceptibility"],
  "prototypeUses": []
}
---

## The supporting forest {#section-support}

<a id="tag-XHFN" data-assertion="proposition" data-title="Almost-sure containment in the positive-probability support"></a><p>Let $G_q$ have edge $\{u,v\}$ precisely when $u\neq v$ and $q_{uv}&gt;0$. Almost surely, every open edge lies in $G_q$. Consequently, if $G_q$ is acyclic, it can serve as the deterministic forest $G$ in this article.</p><p><em>Proof.</em> Each edge of probability zero is closed almost surely. There are only countably many unordered pairs, so almost surely they are all closed simultaneously. Diagonal pairs are discarded when forming the graph. The same countable-null-union argument also shows that the entire configuration lies in the set of positive-probability coordinates almost surely, including its diagonal coordinates.</p>

## Exact connection probabilities {#section-path}

<a id="tag-8KVE" data-assertion="theorem" data-title="Unique-path formula and forest susceptibility"></a><p>If $x$ and $y$ lie in the same component of $G$, let $P_G(x,y)$ denote their unique simple path. Then</p><div class="math-display">$$\tau(x,y)=\prod_{e\in P_G(x,y)}q_e.$$</div><p>If they lie in different components, $\tau(x,y)=0$. In particular,</p><div class="math-display">$$\chi(x)=\sum_{y\text{ in the component of }x}\prod_{e\in P_G(x,y)}q_e,$$</div><p>as an extended nonnegative sum. The path from $x$ to itself is empty, so its product is one and the root always contributes one to $\chi(x)$.</p><p><em>Proof.</em> Work on the probability-one event that the open graph is contained in $G$. Opening every edge of $P_G(x,y)$ connects its endpoints. Conversely, any open connection contains a simple path, and acyclicity forces that path to be $P_G(x,y)$. Thus the connection event agrees almost surely with the finite cylinder specifying that all its path edges are open. Independence gives the product. Disconnected host components cannot be joined by an open path. Finally, summing the connection probabilities gives $\mathbb E|K(x)|$, by summing the indicators of membership in the root cluster.</p>

<p>The path equivalence in the proof is deterministic and holds on an arbitrary vertex set: if the open graph lies in an acyclic host, a connection between the endpoints of a specified host path occurs exactly when all edges of that path are open. Countability is used for the probabilistic support and measurability arguments, not for uniqueness of the path. On the ray, the path from $m$ to $n$ with $m\leq n$ is the sequence $m,m+1,\ldots,n$; it has length $n-m$ and every vertex on it is at most $n$.</p>

<p>Almost-sure containment is essential: an additional positive-probability edge can provide a route avoiding the displayed path. Nor should the forest formula be replaced by a sum over walks, which repeat edges and count the same connection many times.</p>

## The nearest-neighbour ray {#section-ray}

<a id="tag-TGL4" data-assertion="proposition" data-title="Exact two-point function and endpoint susceptibility on the ray"></a><p>On $\mathbb N$, give each bond $\{n,n+1\}$ probability $t\in[0,1]$ and every other non-loop bond probability zero. Then, for all $m,n\in\mathbb N$,</p><div class="math-display">$$\tau(m,n)=t^{|m-n|},\qquad \chi(0)=\sum_{n=0}^{\infty}t^n=\begin{cases}(1-t)^{-1},&amp;0\leq t&lt;1,\\\infty,&amp;t=1.\end{cases}$$</div><p>Here $t^0=1$, including at $t=0$. The endpoint susceptibility is finite exactly when $t&lt;1$.</p><p><em>Proof.</em> The ray is an almost-sure host. Its unique path between $m$ and $n$ has $|m-n|$ edges, so the path formula gives the two-point function. At the endpoint there is one vertex at every distance, and the susceptibility is the geometric series above. At $t=1$ every summand is one.</p>

<p>The <a href="#/binary-tree-percolation">rooted binary tree</a> shows how the same path calculation changes when the number of vertices at distance $n$ grows exponentially. On the ray it is one; on that tree it is $2^n$, so the corresponding susceptibility series is $\sum_n(2t)^n$.</p>

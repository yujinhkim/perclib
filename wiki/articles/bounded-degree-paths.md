---
{
  "id": "bounded-degree-paths",
  "title": "The bounded-degree path criterion",
  "subtitle": "Exclude immediate backtracking before summing paths",
  "kind": "theorem",
  "category": "General theory",
  "summary": "Counting simple paths improves the uniform-degree small-parameter criterion from Delta p below one to (Delta minus one) p below one. The same count bounds susceptibility and includes degrees zero and one.",
  "context": ["A countable simple host graph $G$, with at most $\\Delta$ neighbours at each vertex, where $\\Delta\\in\\mathbb N$.", "Independent bond probabilities $q_e\\leq p\\in[0,1]$ on host edges, and zero on other non-loop pairs.", "Diagonal coordinates are unrestricted; paths and clusters belong to the simple open graph."],
  "related": ["subcritical-bound", "connectivity", "forest-connections", "susceptibility", "binary-tree-percolation"],
  "sourceIds": ["perclib-bounded-degree", "notes"],
  "aliases": ["self-avoiding path", "maximum degree", "nonbacktracking", "path criterion"],
  "prototypeUses": []
}
---

## Count simple paths {#section-count}

<a id="tag-8WML" data-assertion="theorem" data-title="Bounded-degree simple-path count and opening probability"></a>
<p>Put $b=\max\{\Delta-1,0\}$. For every root $x$ and integer $n\geq1$, the number of oriented vertex-simple host paths of length $n$ starting at $x$ is at most $\Delta b^{n-1}$. Consequently,</p>
<div class="math-display">$$\mathbb P_q(\text{there is a simple open path of length }n\text{ from }x)\leq\Delta b^{n-1}p^n=\Delta p\,(bp)^{n-1}.$$</div>
<p>As usual an empty product is one, so the formula includes $n=1$, $b=0$ and $p=0$.</p>
<p><em>Proof.</em> There are at most $\Delta$ choices for the first step. After that, a simple path cannot return immediately to its preceding vertex, leaving at most $\Delta-1$ choices. Avoiding all other previously visited vertices only decreases this number. If $\Delta=0$ there is no first step, and if $\Delta=1$ there is no second step. This proves the count in every case. Each simple path has distinct edges, so independence makes its opening probability the product of its edge probabilities, at most $p^n$. A union bound over the finitely many paths finishes the proof.</p>
<p>The count uses nonbacktracking as an upper bound on simple paths. It does not treat repeated traversals of an edge as independent trials, and it does not require that the host be a tree.</p>

<p>The deterministic path count needs no countability of the vertex set. It constructs a finite family of continuation lists, and the list after the root determines both a path and its endpoint. The fixed-length open-host-path event is consequently a finite union of cylinder events even in an uncountable ambient graph. Its probability bound needs only the edge-probability upper bound on the host; off-host probabilities play no role until one uses host paths to control the full open cluster.</p>

<p>There is also a direct route from these path estimates to nonpercolation. In any locally finite graph, the set of vertices reachable from a fixed root by walks of length at most $n$ is finite: at radius zero it is a singleton, and each further radius is contained in that singleton together with the finitely many corresponding smaller balls around its neighbours. An infinite cluster in a subgraph of this host therefore reaches outside that finite set. Take a simple path to such a vertex and truncate it to obtain a simple open path of any prescribed finite length. Under the host-containment event, the probability of an infinite cluster is thus bounded by $\Delta p\,(bp)^{n-1}$ for every $n\geq1$, which tends to zero if $bp&lt;1$. Local finiteness matters for the deterministic implication: an infinite star has an infinite cluster when all its edges are open, but no simple path of length three.</p>

## Sum over lengths {#section-susceptibility}

<a id="tag-YP44" data-assertion="corollary" data-title="Susceptibility and nonpercolation under the bounded-degree criterion"></a>
<p>Under the same assumptions, if $r=bp&lt;1$, then for every root $x$,</p>
<div class="math-display">$$\chi_q(x)\leq1+\frac{\Delta p}{1-r}.$$</div>
<p>With probability one, all open clusters are finite. For $\Delta\geq1$ the criterion is $(\Delta-1)p&lt;1$. For $\Delta=0$ it holds at every $p$ and gives $\chi_q(x)=1$; for $\Delta=1$ it gives $\chi_q(x)\leq1+p$ even at $p=1$.</p>
<p><em>Proof.</em> Almost surely every open non-loop edge belongs to the host: there are only countably many zero-probability off-host coordinates. On that event a connection from $x$ to another vertex has a simple host path as a witness. Sum the path union bound over endpoints and lengths. Every oriented path from $x$ has exactly one endpoint, so</p>
<div class="math-display">$$\chi_q(x)=\sum_y\mathbb P_q(x\leftrightarrow y)\leq1+\sum_{n\geq1}\Delta p\,r^{n-1}=1+\frac{\Delta p}{1-r}.$$</div>
<p>The root contributes the initial one. All sums are nonnegative, so their rearrangement needs no prior finiteness assumption. Finite expected extended cluster volume excludes an infinite cluster at a fixed root. Countability of the vertex set makes this conclusion simultaneous over all roots.</p>
<p>For $\Delta\geq2$, a homogeneous $\Delta$-regular tree attains the susceptibility bound when $r&lt;1$: it has exactly $\Delta(\Delta-1)^{n-1}$ vertices at distance $n\geq1$, each reached along its unique path with probability $p^n$. When $r\geq1$, the same series diverges. Infinite susceptibility alone does not imply an infinite cluster, so this calculation makes no assertion about percolation at the boundary $r=1$.</p>

## Comparison with a row bound {#section-comparison}

<p>The uniform row estimate gives $\sum_yq_{xy}\leq\Delta p$, so its direct geometric criterion requires $\Delta p&lt;1$. The path count improves this to $(\Delta-1)p&lt;1$ when $\Delta\geq1$ by removing the immediate reversal at each later step. The <a href="/tag/53Z9/">row-sum theorem</a> is more flexible: it also treats infinitely many possible neighbours when their probabilities have a summable uniform row. A degree bound is a different hypothesis.</p>
<p>For nearest-neighbour bonds on $\mathbb Z^d$, $d\geq1$, the neighbours of a vertex are its $2d$ distinct translates by the positive and negative coordinate vectors. Thus the criterion gives no infinite cluster when $(2d-1)p&lt;1$. The inspected library's lattice corollary takes the degree estimate as an explicit input; the elementary count just given supplies the mathematical reason for that input.</p>

<p>This proves the lower-bound mechanism in the notes' non-triviality proposition. Its planar upper-bound argument is a separate part of that proposition and is not covered here.</p>

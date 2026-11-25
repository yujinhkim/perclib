---
{
  "id": "connectivity",
  "title": "Connectivity and clusters",
  "subtitle": "Finite witnesses inside an infinite probability space",
  "kind": "concept",
  "category": "Foundations",
  "summary": "Connectivity has finite path witnesses. Keeping restricted connectivity distinct from cluster intersection prevents several common ambiguities.",
  "context": [
    "Independent bond percolation on a countable undirected simple graph.",
    "A distinguished vertex $v$ when a rooted cluster is used."
  ],
  "related": [
    "susceptibility",
    "subcritical-bound",
    "criticality",
    "exploration",
    "universal-tightness"
  ],
  "sourceIds": [
    "grimmett",
    "heydenreich-hofstad",
    "notes"
  ],
  "aliases": [
    "reachability",
    "open path",
    "cluster",
    "restricted connectivity",
    "finite volume",
    "K Lambda"
  ],
  "prototypeUses": [
    "product-model"
  ]
}
---

## Connection events {#section-paths}

<a id="tag-T90E" data-assertion="definition" data-title="Connection through finite open paths"></a><p>For an edge configuration under the <a href="#/product-model">product percolation law</a>, write $x\leftrightarrow y$ when there is a finite path of open edges from $x$ to $y$. The path of length zero is allowed, so $x\leftrightarrow x$ always holds. Removing loops from any connecting walk gives a vertex-simple path witness.</p><a id="tag-6WC8" data-assertion="definition" data-title="Root cluster and two-point function"></a><div class="math-display">$$K_v(\omega)=\{w\in V:v\leftrightarrow w\},\qquad \tau_q(v,w)=\mathbb P_q(v\leftrightarrow w).$$</div><a id="tag-7QJG" data-assertion="proposition" data-title="Measurability of connection events"></a><p>Since a countable graph has countably many finite paths, the connection event is a countable union of cylinder events. It is therefore measurable. This argument does not require the host graph to have finite degrees.</p><p>Counting simple path witnesses gives the <a href="#/subcritical-bound">row-sum susceptibility bound</a>.</p>

## Three different objects {#section-restriction}

<a id="tag-OG96" data-assertion="definition" data-title="Restricted cluster and full-cluster intersection"></a><p>For a region $\Lambda\subseteq V$ containing $v$, distinguish</p><div class="math-display">$$K_v^\Lambda=\{w\in\Lambda:v\mathrel{\mathop{\leftrightarrow}\limits^\Lambda}w\},\qquad K_v\cap\Lambda,\qquad K_v.$$</div><a id="tag-HQ6X" data-assertion="proposition" data-title="Restricted clusters lie in full-cluster intersections"></a><p>The first uses paths whose vertices all lie in $\Lambda$. The second may connect two vertices of $\Lambda$ by an excursion outside it. Consequently $K_v^\Lambda\subseteq K_v\cap\Lambda$, but equality need not hold.</p><p>For example, take a path $v-a-w$ with $\Lambda=\{v,w\}$ and $a\notin\Lambda$. If both edges are open, $w$ belongs to $K_v\cap\Lambda$ but not to $K_v^\Lambda$.</p>

## Exhaustion by finite regions {#section-exhaustion}

<a id="tag-5UJQ" data-assertion="proposition" data-title="Connectivity under finite exhaustion"></a><p>Let $\Lambda_n$ be increasing finite regions whose union is $V$. Every finite connecting path eventually lies in some $\Lambda_n$. Thus, once both endpoints are included,</p><div class="math-display">$$\{x\leftrightarrow y\}=\bigcup_n\{x\mathrel{\mathop{\leftrightarrow}\limits^{\Lambda_n}}y\}.$$</div><p>Continuity of probability from below identifies infinite-volume connectivity with the limit of these finite-volume events. This is a recurring bridge from finite combinatorics to countable models.</p>

## Possibly infinite volume {#section-volume}

<a id="tag-5SII" data-assertion="proposition" data-title="Extended cluster volume and measurability"></a><p>The cardinality $|K_v|$ takes values in $\mathbb N\cup\{\infty\}$. <a href="#/criticality">Infinite-cluster events</a> are measurable, for example by expressing $|K_v|\ge n$ through finite sets of connected vertices. Keep this extended cardinality until a theorem proves finiteness.</p><p>Its expectation leads to <a href="#/susceptibility">susceptibility</a>; finite path witnesses also support <a href="#/exploration">exploration algorithms</a> and <a href="#/universal-tightness">largest-cluster estimates</a>.</p>

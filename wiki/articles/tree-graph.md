---
{
  "id": "tree-graph",
  "title": "The three-point tree-graph inequality",
  "subtitle": "Splitting a connected triple at a branch point",
  "kind": "theorem",
  "category": "Inequalities",
  "summary": "A joint connection probability is bounded by a sum of products of three two-point functions, without transitivity or distinctness assumptions.",
  "context": ["A countable vertex set $V$ with independent bond probabilities $q_e\\in[0,1]$.", "The open graph discards loops; diagonal probabilities are unrestricted.", "$\\tau(u,v)=\\mathbb P(u\\leftrightarrow v)$, with $\\tau(u,u)=1$."],
  "related": ["connectivity", "disjoint-occurrence", "susceptibility", "triangle-condition"],
  "sourceIds": [],
  "aliases": ["tree graph", "Aizenman Newman", "three point", "branch point"],
  "prototypeUses": []
}
---

## Three connections from one vertex {#section-bound}

<a id="tag-L82Q" data-assertion="theorem" data-title="Three-point tree-graph inequality"></a><p>For every independent bond profile on a countable vertex set and all $x,y,z\in V$,</p><div class="math-display">$$\mathbb P(x\leftrightarrow y,\ x\leftrightarrow z)\leq\sum_{w\in V}\tau(x,w)\tau(w,y)\tau(w,z).$$</div><p>The vertices need not be distinct. The sum is an extended nonnegative sum and may be infinite; no summability or transitivity hypothesis is imposed.</p>

<p><em>Proof.</em> First retain only a finite set of bonds. On the event on the left, the union of open paths connecting $x$ to $y$ and $z$ contains a finite tree connecting the three vertices. In its minimal connecting subtree there is a vertex $w$ from which the paths to $x$, $y$ and $z$ are pairwise edge-disjoint. If vertices coincide, take the corresponding paths to have length zero. Their edge sets are disjoint open witnesses for the three connection events. The van den Berg–Kesten inequality for increasing events on finitely many independent coordinates, quoted here as a cited result rather than proved in this article, bounds disjoint occurrence by the product of probabilities. Applying it twice, using <a href="/tag/HP3X/">associativity of disjoint occurrence</a>, bounds the three-event disjoint occurrence by the product of the three connection probabilities. A union bound over $w$ gives the inequality for the restricted configuration.</p>

<p>Now exhaust all non-loop bonds by increasing finite sets. Any connection, or simultaneous pair of connections, has a finite path witness, so the restricted joint probabilities increase to the probability on the left. Each restricted two-point function is bounded by its full-model counterpart. Thus every finite restriction has the same upper bound displayed above, and passage to the limit proves the assertion. This argument uses only finite-coordinate BK; it does not assume an infinite-volume BK theorem.</p>

## Repeated vertices {#section-endpoints}

<p>The diagonal convention matters. If $y=x$, the left side is $\tau(x,z)$, and the summand $w=x$ already equals $\tau(x,z)$. On two vertices joined by an edge of probability $t$, taking $x$ to be one vertex and $y=z$ the other gives left side $t$ and right side $t^2+t$. These cases require neither strict positivity nor an exclusion of repeated vertices.</p>

<p>This article supplies the exact statement requested in <a href="https://github.com/tomhutchcroft/lrp/issues/226">the tree-graph interface package</a>. Its proposed Aizenman–Newman and Grimmett locators remain to be checked; no edition-specific source occurrence is asserted here.</p>

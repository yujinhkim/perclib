---
{
  "id": "exploration",
  "title": "Exploration and deferred decisions",
  "subtitle": "Reveal enough to answer the question",
  "kind": "method",
  "category": "Methods",
  "summary": "Adaptive exploration turns a static product measure into a sequence of revealed coordinates while preserving the laws of coordinates not yet examined.",
  "context": [
    "Begin with finitely many independent edge coordinates.",
    "At each step, the next coordinate is chosen using only the revealed history and independent auxiliary randomness.",
    "An edge is not revealed a second time."
  ],
  "related": [
    "subcritical-bound",
    "sharpness",
    "finite-random-graphs",
    "cutoff-families"
  ],
  "sourceIds": [
    "grimmett",
    "heydenreich-hofstad",
    "notes"
  ],
  "aliases": [
    "BFS",
    "DFS",
    "deferred decisions",
    "revealment",
    "decision trees",
    "OSSS",
    "resampling"
  ],
  "prototypeUses": [
    "product-model",
    "connectivity"
  ]
}
---

## The deferred-decision principle {#section-principle}

<a id="tag-GSLG" data-assertion="proposition" data-title="Deferred decisions under adaptive exploration"></a><p>Consider an exploration that reveals one edge at a time. Conditional on any possible finite history, the unrevealed edges retain their original <a href="#/product-model">independent Bernoulli laws</a>. The choice of the next edge may be adaptive: it can depend on every value seen so far.</p><p>For a fixed realised history, the required revealed values impose cylinder conditions. The selection rule has used only those values and independent auxiliary randomness, so it has not inspected the remaining coordinates. The product formula therefore gives the conditional law of the remainder.</p>

## Exploring a cluster {#section-cluster}

<a id="tag-7WHX" data-assertion="proposition" data-title="Termination of cluster exploration identifies the root cluster"></a><p>In a finite graph, begin with the root discovered. Reveal an unexplored edge from the discovered region; an open edge may discover a new vertex. Continue until no unexplored boundary edge remains. At termination the discovered set is exactly the <a href="#/connectivity">root cluster</a>.</p><p>The algorithm provides more than a way to sample the cluster. It identifies which coordinates determine an event and supplies revealment probabilities. Different exploration orders can be useful for different inequalities even though they reveal the same final component.</p>

## Why branching comparisons appear {#section-comparison}

<p>An exploration offers possible new neighbours, but some offers lead to vertices already discovered. Ignoring these collisions suggests a branching comparison. To turn that suggestion into a proof, specify the conditional law of each offer and an actual domination or coupling.</p><p>The <a href="#/subcritical-bound">row-sum theorem</a> avoids such a coupling by counting paths directly. Both methods explain why a mean number of possible onward connections below one is a natural subcritical condition.</p>

## Decision trees and broader applications {#section-uses}

<p>Exploration provides revealed and unrevealed regions in <a href="#/sharpness">sharpness proofs</a>, entropy comparison, OSSS inequalities, and conditional resampling. Differential arguments for <a href="#/cutoff-families">cutoff families</a> combine such decompositions with a separate Russo formula. Each application specifies its stopping rule, the event being determined, and the meaning of revealment.</p><p>On an infinite host, merely saying “inspect all neighbours” need not define a finite step. Finite-volume approximations, coordinate enumerations, and limits of stopping procedures must be specified. Conditional independence of two resampled continuations also does not imply that their edge witnesses are disjoint.</p><p>For <a href="#/finite-random-graphs">finite random graphs</a>, the exploration history turns the component problem into a process with explicit conditional transition laws.</p>

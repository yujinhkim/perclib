---
{
  "id": "finite-transcripts",
  "title": "Finite exploration transcripts",
  "subtitle": "Conditioning on answers to adaptive queries",
  "kind": "method",
  "category": "Methods",
  "summary": "A fixed adaptive transcript is a cylinder event. Its probability factors over the queried coordinates, and the remaining coordinates keep their product law whenever conditioning is defined.",
  "context": [
    "An arbitrary coordinate set $I$ with product Bernoulli law $\\mathbb P_q$.",
    "A deterministic query rule whose next coordinate depends only on previous answers.",
    "Finitely many queries, with distinct coordinates along the transcript under consideration."
  ],
  "related": [
    "exploration",
    "product-model",
    "connectivity",
    "russo-formula"
  ],
  "sourceIds": [
    "mathlib",
    "notes",
    "perclib-configuration-conditioning",
    "perclib-block-independence",
    "perclib-boundary-wiring",
    "perclib-exploration-transcripts"
  ],
  "aliases": [
    "transcript",
    "adaptive queries",
    "decision tree",
    "deferred decisions",
    "unrevealed coordinates"
  ],
  "prototypeUses": []
}
---

## A fixed transcript {#section-fixed}

<p>Let $e_0,\ldots,e_{n-1}$ be coordinates and let $b=(b_0,\ldots,b_{n-1})\in\{0,1\}^n$. The transcript event is</p><div class="math-display">$$T(e,b)=\{\omega:\mathbf1_{\{e_k\in\omega\}}=b_k\text{ for every }k&lt;n\}.$$</div><p>Write $S=\{e_0,\ldots,e_{n-1}\}$, and set $w_i(1)=q_i$ and $w_i(0)=1-q_i$. This notation includes probabilities zero and one without powers of zero.</p>

<a id="tag-EE11" data-assertion="proposition" data-title="Finite transcript probability and factorization"></a><p>If $e_0,\ldots,e_{n-1}$ are distinct, the transcript has probability</p><div class="math-display">$$\mathbb P_q(T(e,b))=\prod_{k=0}^{n-1}w_{e_k}(b_k).$$</div><p>For every measurable event $B$ on the coordinates $I\setminus S$, with restriction map $\rho_{I\setminus S}$,</p><div class="math-display">$$\mathbb P_q\bigl(T(e,b)\cap\rho_{I\setminus S}^{-1}(B)\bigr)=\mathbb P_q(T(e,b))\,\mathbb P_{q|_{I\setminus S}}(B).$$</div><p><em>Proof.</em> The first equality is the finite cylinder formula. For the second, the two events use disjoint coordinate sets. Product factorization proves the equality first when $B$ is a cylinder. The collection of measurable $B$ for which it holds is a Dynkin system containing the cylinder pi-system, so it contains the product sigma-algebra. No division by the transcript probability is needed.</p><p>When $n=0$, the transcript is the whole space and the empty product is one. Distinctness is essential to the product formula: querying one coordinate twice and receiving two open answers has probability $q_i$, not $q_i^2$.</p>

<p>Bond-coordinate transcripts may include diagonal pairs. For example, observing the loop $\{x,x\}$ open and the distinct pair $\{x,y\}$ closed, with $y\ne x$, has probability $q_{\{x,x\}}(1-q_{\{x,y\}})$. This concerns the full configuration law; discarding loops from the simple graph does not erase them from the product probability space.</p>

## Why adaptive queries give cylinders {#section-adaptive}

<p>For each $k&lt;n$, let $a_k:\{0,1\}^k\to I$ choose the next coordinate from the preceding answers. The actual answers are defined recursively by</p><div class="math-display">$$B_k(\omega)=\mathbf1_{\{a_k(B_0(\omega),\ldots,B_{k-1}(\omega))\in\omega\}}.$$</div><p>For a fixed proposed answer string $b$, all its queries are fixed coordinates: put $e_k(b)=a_k(b_0,\ldots,b_{k-1})$.</p>

<a id="tag-86IX" data-assertion="proposition" data-title="Adaptive transcript cylinder identity"></a><p>For every $b\in\{0,1\}^n$,</p><div class="math-display">$$\{\omega:(B_0(\omega),\ldots,B_{n-1}(\omega))=b\}=T(e(b),b).$$</div><p>This identity does not require distinct queries. If the coordinates $e_k(b)$ are distinct, the probability and factorization formulas above therefore apply to the adaptive transcript.</p><p><em>Proof.</em> On the event that the answers equal $b$, the recursion queries $e_k(b)$ at every step and sees $b_k$, giving one inclusion. Conversely, suppose all the prescribed coordinate values hold. The zeroth query has no history and returns $b_0$. If the first $k$ answers agree with $b$, the next query is $e_k(b)$ and returns $b_k$. Induction gives the entire answer string.</p><p>The no-repeat condition is needed only along the fixed string in question. One need not assume that the query coordinates selected on different branches are disjoint. A stopping rule determined by the observed answers is handled at each terminal string by taking $n$ to be its length; the event of reaching that leaf is exactly its transcript cylinder. The statement does not cover a stopping rule that secretly inspects unrevealed coordinates.</p>

## The conditional law and its limits {#section-conditioning}

<a id="tag-56TE" data-assertion="corollary" data-title="Conditional product law after a positive-probability transcript"></a><p>Fix a transcript $b$ with distinct queries and positive probability. Given that transcript, the restriction to its unqueried coordinates has product Bernoulli law with the original parameters:</p><div class="math-display">$$\mathbb P_q\bigl(\rho_{I\setminus S(b)}(\omega)\in B\mid (B_0,\ldots,B_{n-1})=b\bigr)=\mathbb P_{q|_{I\setminus S(b)}}(B)$$</div><p>for every measurable $B$, where $S(b)=\{e_k(b):k&lt;n\}$. This is the factorization formula divided by the positive transcript probability. For a zero-probability transcript, factorization still holds, but this division does not define a conditional law.</p><p>This makes the <a href="/tag/GSLG/">deferred-decision principle</a> precise for deterministic finite queries. It does not say that the random set of queried coordinates is independent of the answers. For example, query coordinate $1$, then query $2$ if the first answer is open and $3$ otherwise. The queried set itself reveals the first answer.</p><p>An independently randomized query rule can be treated by fixing its auxiliary randomness and applying the deterministic argument, then integrating where the requisite measurability holds. The formulas here concern deterministic rules and do not assert a regular conditional distribution for arbitrary auxiliary spaces. Infinite runs likewise need a separate limiting argument; finitely many queries do not justify conditioning on a completed infinite exploration.</p>

<p>The <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L2159">notes use this conditional Bernoulli law in the entropy chain rule for adaptive exploration</a>. The entropy inequality requires additional estimates; it is not a consequence of transcript factorization alone.</p>

## Countable configuration spaces {#section-standard-borel}

<a id="tag-784S" data-assertion="theorem" data-title="Countable configuration spaces are standard Borel"></a>
<p>If $I$ is countable, the configuration space $\{0,1\}^I$, with the sigma-algebra generated by its coordinate maps, is a standard Borel space. In particular this applies to bond configurations on a countable vertex set, including diagonal coordinates.</p>
<p><em>Proof.</em> Choose an injection $j:I\to\mathbb N$ and put</p>
<div class="math-display">$$d(\omega,\eta)=\sum_{i\in I}2^{-j(i)-1}|\omega_i-\eta_i|.$$</div>
<p>This metric induces the product topology. Agreement on all coordinates with $j(i)&lt;m$ makes the distance at most $2^{-m}$, whereas a sufficiently small metric ball fixes any prescribed finite set of coordinates. A Cauchy sequence eventually stabilizes at each coordinate. Its coordinatewise limit is its metric limit, by splitting the sum into finitely many coordinates and a uniformly small tail; thus the metric is complete. Configurations with finite open support form a countable dense set. The finite cylinders are a countable topological base, so the Borel sigma-algebra is exactly the coordinate sigma-algebra. This is a Polish realization of the given measurable space. The empty index set gives a one-point space.</p>
<p>The countability here is a condition on the index set, not on the set of configurations. The latter is uncountable when $I$ is countably infinite. No claim about arbitrary uncountable index sets is needed.</p>

## Conditioning on a fixed coordinate set {#section-fixed-kernel}

<a id="tag-D9KI" data-assertion="theorem" data-title="An explicit conditional kernel for a fixed set of observed coordinates"></a>
<p>Let $I$ be countable, let $S\subseteq I$ be deterministic, and write $\mu_S=\mathbb P_{q|_S}$ and $\mu_{S^c}=\mathbb P_{q|_{I\setminus S}}$. For $\eta\in\{0,1\}^S$ and $\xi\in\{0,1\}^{I\setminus S}$, let $\eta\oplus\xi$ be their combined configuration. Then</p>
<div class="math-display">$$K(\eta,A)=\int\mathbf1_A(\eta\oplus\xi)\,\mu_{S^c}(d\xi)$$</div>
<p>is a probability kernel from the observed configurations to full configurations, and for every measurable $A\subseteq\{0,1\}^I$ and $B\subseteq\{0,1\}^S$,</p>
<div class="math-display">$$\mathbb P_q\bigl(\omega\in A,\ \omega|_S\in B\bigr)=\int_B K(\eta,A)\,\mu_S(d\eta).$$</div>
<p>Thus $K$ is a version of the conditional law of the full configuration given its restriction to $S$. It fixes the observed coordinates and leaves the complement with its original product law, for finite or infinite $S$.</p>
<p><em>Proof.</em> The assembly map $(\eta,\xi)\mapsto\eta\oplus\xi$ is measurable because each output coordinate is a coordinate of one of its arguments. For fixed $\eta$, its pushforward of $\mu_{S^c}$ is a probability measure. The integral defining $K(\eta,A)$ is measurable in $\eta$ by the measurable-parameter integration theorem, so $K$ is a kernel. The full product law is the pushforward of $\mu_S\otimes\mu_{S^c}$ under assembly: both measures have the same probabilities on finite cylinders. Fubini applied to $\mathbf1_B(\eta)\mathbf1_A(\eta\oplus\xi)$ gives the displayed identity.</p>
<p>This formula specifies a kernel even at observed configurations of probability zero; it does not divide by their probabilities. With $S$ finite and a positive-probability observation, it reduces to the transcript conditional law above. At $S=\varnothing$ it is the original law, and at $S=I$ it is the point mass at the observed configuration.</p>
<p>The set $S$ is fixed before sampling. For an adaptive exploration, a particular finite transcript fixes such a set, as proved above, but the random queried set cannot simply be substituted into this theorem. A completed infinite adaptive exploration requires its own measurability and conditional-law argument. Standard-Borel structure supplies a setting for conditional distributions; it does not supply that independence argument.</p>

## Independence of fixed coordinate blocks {#section-blocks}

<a id="tag-DYU8" data-assertion="theorem" data-title="Measurable observables of disjoint blocks are independent"></a>
<p>Let $I$ be any coordinate set and let $S,T\subseteq I$ be disjoint deterministic subsets, possibly infinite. Under $\mathbb P_q$, the restrictions $\rho_S(\omega)=\omega\cap S$ and $\rho_T(\omega)=\omega\cap T$ are independent random configurations with their respective product sigma-algebras. In particular, for measurable events $A\subseteq2^S$ and $B\subseteq2^T$,</p>
<div class="math-display">$$\mathbb P_q(\rho_S\in A,\rho_T\in B)=\mathbb P_{q|_S}(A)\mathbb P_{q|_T}(B).$$</div>
<p>More generally, if $f:2^S\to X$ and $g:2^T\to Y$ are measurable maps to measurable spaces, then $f(\rho_S)$ and $g(\rho_T)$ are independent. The coordinate membership variables are mutually independent, meaning that every finite subfamily has its product law.</p>
<p><em>Proof.</em> Restriction is measurable because each output coordinate is an original coordinate. Finite cylinders determine its product law, even when the block is infinite. For cylinders $A$ and $B$, their coordinate sets are disjoint, so the joint probability is the product of their probabilities. Fix a cylinder $A$. The measurable $B$ satisfying this equality form a Dynkin system containing the cylinder pi-system on $T$; hence the equality holds for every measurable $B$. Now fix any such $B$ and repeat the argument on $S$. This proves independence of the restrictions. Apply the factorization to inverse images of measurable sets under $f$ and $g$ for independence of their observables. The finite-cylinder formula also gives the asserted mutual independence of individual coordinates.</p>
<p>For instance, the negative and nonnegative integer coordinates give two independent infinite blocks, for any inhomogeneous profile. An empty block is deterministic; coordinates with probability zero or one cause no exception. Neither the ambient index set nor either block needs to be countable. Measurability in the product sigma-algebras is essential.</p>
<p>The blocks here are fixed sets. Independence does not follow merely because two random queried sets happen to be disjoint; the choice of a set can reveal coordinate values. The earlier transcript factorization accounts for that choice by first fixing the transcript.</p>

## Families of disjoint blocks {#section-block-families}

<a id="tag-QH7Q" data-assertion="proposition" data-title="Injective coordinate sampling, independent block families and countable closed products"></a>
<p>Let $I,J$ be arbitrary sets, let $q\in[0,1]^I$, and let $e:J\to I$ be injective. The sampled configuration $\{j:e(j)\in\omega\}$ is measurable and has product law with profile $q\circ e$. If $(S_b)_{b\in B}$ is any pairwise disjoint family of coordinate subsets, their restrictions are mutually independent: every finite family of measurable block events has joint probability equal to the product of its probabilities. The same is true of measurable observables of these blocks.</p>
<p>For a countable $T\subseteq I$,</p>
<div class="math-display">$$\mathbb P_q(\omega\cap T=\varnothing)=\prod_{i\in T}(1-q_i),$$</div>
<p>where the product is the limit of finite products along any increasing finite exhaustion. If $q_i=1-e^{-\beta J_i}$ on $T$, with finite $\beta\geq0$, nonnegative $J_i$ and $\sum_{i\in T}J_i&lt;\infty$, this probability is $\exp(-\beta\sum_{i\in T}J_i)$.</p>
<p><em>Proof.</em> Sampling is measurable coordinate by coordinate. Injectivity means that distinct sampled coordinates read distinct original coordinates, so every finite cylinder has the required product probability. Cylinder uniqueness identifies the sampled law.</p>
<p>For finitely many blocks, prove the factorization by induction. One block is disjoint from the union of all the others; by <a href="/tag/DYU8/">fixed-block independence</a>, its event is independent of the intersection of the other events, which is a measurable event of their union block. The induction hypothesis factors that intersection. Measurable observables preserve the factorization by taking inverse images. Since mutual independence is defined through finite subfamilies, this covers arbitrary $B$.</p>
<p>For countable $T$, the finite all-closed events decrease to $\{\omega\cap T=\varnothing\}$. Continuity from above and finite independence give the product formula. In the exponential case, each finite product equals the exponential of the corresponding negative intensity sum; summability and continuity give its limit. The empty product is one, and a coordinate of probability one makes the closed product zero.</p>
<p>With one vertex $x$ fixed, the map $y\mapsto\{x,y\}$ is injective, even when $y=x$ is allowed. Thus the closed-product formula applies to any countable collection of such pairs. If the targets include $x$, the diagonal coordinate participates in that configuration event, although it never contributes an edge to the simple graph. Boundary wiring uses the special case $x\in S$, with targets in $V\setminus S$, so no such diagonal occurs.</p>

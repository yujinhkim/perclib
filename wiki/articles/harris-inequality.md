---
{
  "id": "harris-inequality",
  "title": "The Harris inequality",
  "subtitle": "Positive association under a product law",
  "kind": "theorem",
  "category": "Foundations",
  "summary": "Increasing events under a product Bernoulli law are positively associated; finite witnesses connect this inequality to paths, escape and infinite clusters.",
  "context": [
    "An index set $I$ and a profile $q:I\\to[0,1]$.",
    "Configurations $\\omega\\subseteq I$, with the product sigma-algebra and product Bernoulli law.",
    "Countability is imposed only for the finite-witness and graph applications."
  ],
  "related": [
    "product-model",
    "connectivity",
    "susceptibility"
  ],
  "sourceIds": [
    "notes",
    "grimmett",
    "mathlib",
    "perclib-open-event-harris"
  ],
  "aliases": [
    "Harris",
    "FKG",
    "positive association",
    "increasing events",
    "finite open witnesses"
  ],
  "prototypeUses": [
    "product-model"
  ]
}
---

## Increasing events {#section-increasing}

<a id="tag-H4OA" data-assertion="definition" data-title="Increasing events and observables"></a><p>Order configurations by inclusion: $\omega\leq\omega'$ if every coordinate open in $\omega$ is also open in $\omega'$. An event $A$ is <em>increasing</em> if $\omega\in A$ and $\omega\leq\omega'$ imply $\omega'\in A$. A real-valued observable $f$ is increasing if $f(\omega)\leq f(\omega')$ whenever $\omega\leq\omega'$.</p><p>Connection events are increasing: opening more edges preserves every existing open path. Measurability is a separate requirement. On an infinite product space, it must be established before applying a probability inequality.</p>

## Positive association {#section-harris}

<a id="tag-X5SS" data-assertion="theorem" data-title="Harris inequality for product Bernoulli measures"></a><p>Let $I$ be any index set and let $\mathbb P_q$ be the product Bernoulli law with profile $q:I\to[0,1]$. If $A$ and $B$ are increasing measurable events, then</p><div class="math-display">$$\mathbb P_q(A\cap B)\geq\mathbb P_q(A)\mathbb P_q(B).$$</div><p>No coordinate probability is required to lie strictly between zero and one. The finite-coordinate proof uses the corresponding inequality for bounded increasing real-valued functions.</p><p><em>Proof.</em> For one coordinate with open probability $p$, direct expansion gives</p><div class="math-display">$$\mathbb E[fg]-\mathbb E[f]\mathbb E[g]=p(1-p)\bigl(f(1)-f(0)\bigr)\bigl(g(1)-g(0)\bigr)\geq0.$$</div><p>For finitely many coordinates, integrate out all but one. The induction hypothesis bounds the conditional average of $fg$ below by the product of the two conditional averages. Those averages are increasing functions of the remaining coordinate, since the other coordinates are integrated against the same product law at both values. The one-coordinate inequality completes the induction.</p><p>For an arbitrary index set, put $f=\mathbf1_A$ and $g=\mathbf1_B$. For finite $F\subseteq I$, average over the coordinates outside $F$, writing the resulting functions as $f_F$ and $g_F$. They are measurable increasing functions of the coordinates in $F$, and their expectations equal those of $f$ and $g$.</p><p>Bounded cylinder functions are dense in $L^1$ of the product sigma-algebra. Indeed, the events approximable in measure by finite-coordinate events form a sigma-algebra containing the cylinder algebra. If a cylinder function $h$ depends on $F_0$ and $F\supseteq F_0$, contraction of conditional averaging gives</p><div class="math-display">$$\|f_F-f\|_1\leq\|(f-h)_F\|_1+\|h-f\|_1\leq2\|f-h\|_1.$$</div><p>Thus, given $\varepsilon>0$, one finite set $F$ makes both $\|f_F-f\|_1$ and $\|g_F-g\|_1$ smaller than $\varepsilon$. Since all four functions take values in $[0,1]$,</p><div class="math-display">$$\bigl|\mathbb E[f_Fg_F]-\mathbb E[fg]\bigr|\leq\|f_F-f\|_1+\|g_F-g\|_1.$$</div><p>Apply the finite-coordinate inequality to $f_F,g_F$ and let $\varepsilon$ decrease to zero. This gives the event inequality. This argument uses finite subsets of $I$, not an enumeration, so countability is unnecessary. The integration and conditional-averaging steps use the usual product-measure and Fubini theorems.</p><a id="tag-22S9" data-assertion="corollary" data-title="Positive association for finitely many increasing events"></a><p>For increasing measurable events $A_1,\ldots,A_n$,</p><div class="math-display">$$\mathbb P_q\!\left(\bigcap_{j=1}^n A_j\right)\geq\prod_{j=1}^n\mathbb P_q(A_j).$$</div><p>Apply Harris inductively, since an intersection of increasing measurable events is again increasing and measurable. For $n=0$, both sides are one.</p>

## Finite open witnesses {#section-witnesses}

<a id="tag-5CN6" data-assertion="proposition" data-title="Measurability from finite open witnesses"></a><p>Suppose $I$ is countable and $A$ is increasing. Assume that every $\omega\in A$ contains a finite set $F\subseteq\omega$ such that the configuration consisting of exactly the open coordinates in $F$ belongs to $A$. Then $A$ is measurable.</p><p>For a finite set $F$, write $U_F=\{\omega:F\subseteq\omega\}$. The witness assumption and monotonicity give</p><div class="math-display">$$A=\bigcup_{\substack{F\subseteq I\text{ finite}\\F\in A}}U_F.$$</div><p>There are countably many finite subsets of $I$, and each $U_F$ is a cylinder event. This proves measurability. Consequently Harris applies to two such events without an additional measurability assumption. Countability is used in this measurability argument, although it was not needed in Harris itself.</p><p>For bond percolation on a countable vertex set, an open path supplies a finite witness for connection. The event that $x$ connects to some vertex outside a set $S$ likewise has a finite witness: retain the edges of one path to a vertex outside $S$. The path need not remain in $S$ before its endpoint, and no finiteness assumption on $S$ is needed.</p>

## Connection and escape {#section-connections}

<a id="tag-UPFU" data-assertion="corollary" data-title="Three-point lower bound from positive association"></a><p>For bond percolation on a countable vertex set and any vertices $x,y,z$, the two-point function satisfies</p><div class="math-display">$$\tau_q(x,z)\geq\tau_q(x,y)\tau_q(y,z).$$</div><p>Both connection events are increasing and measurable, so Harris bounds the probability of their intersection below by the product. Their intersection is contained in $\{x\leftrightarrow z\}$, by concatenating the two paths. Distinctness of the vertices is not required.</p><p>Write $E_S(x)=\{x\leftrightarrow V\setminus S\}$. Each $E_S(x)$ is increasing and measurable by the finite-witness argument. The infinite-cluster event is</p><div class="math-display">$$\{|K_x|=\infty\}=\bigcap_{\substack{S\subseteq V\text{ finite}}}E_S(x).$$</div><p>An infinite cluster meets the complement of every finite set; a finite cluster fails the escape event for $S=K_x$. Since $V$ is countable, the displayed intersection is countable. Thus the infinite-cluster event is also increasing and measurable, and Harris applies to pairs of these events as well as to connection and escape events.</p><p>Escaping one finite set is not the same as having an infinite cluster. On a graph with just one edge $\{x,y\}$, the cluster of $x$ escapes $\{x\}$ whenever that edge is open, but it is always finite. Harris supplies positive association between increasing events; it does not assert their independence.</p>

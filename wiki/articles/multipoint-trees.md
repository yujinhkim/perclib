---
{
  "id": "multipoint-trees",
  "title": "Multipoint tree-graph bounds",
  "subtitle": "Tree-graph upper bounds and multiscale lower bounds",
  "kind": "theorem",
  "category": "Inequalities",
  "summary": "Disjoint tree witnesses give cluster-moment upper bounds. Sweep geometry organizes planar and long-range lower bounds; localization and small-cluster negligibility supply the mass needed for long-range joining.",
  "context": [
    "Independent bond percolation on a nonempty countable vertex set $V$.",
    "The profile may be inhomogeneous and may take the values zero and one; loops are discarded.",
    "$\\tau(x,y)=\\mathbb P(x\\leftrightarrow y)$, with $\\tau(x,x)=1$."
  ],
  "related": [
    "connectivity",
    "disjoint-occurrence",
    "susceptibility",
    "sharpness",
    "mesoscopic-tail-transfer",
    "cutoff-localization",
    "size-biased-laws"
  ],
  "sourceIds": [
    "notes",
    "hutchcroft-lrp-2"
  ],
  "aliases": [
    "multipoint connection",
    "tree-graph moment inequality",
    "binary tree topologies",
    "double-factorial moments",
    "multiscale cluster gluing",
    "long-range multipoint lower bound"
  ],
  "prototypeUses": []
}
---

## The tree shapes {#section-shapes}

<a id="tag-SO5J" data-assertion="proposition" data-title="Counting leaf-labelled trivalent tree shapes"></a>
<p>For an integer $k\geq2$, let $\mathcal T_k$ consist of isomorphism classes of finite unrooted trees whose leaves have the distinct labels $1,\ldots,k$ and whose other vertices all have degree three. Isomorphisms preserve the leaf labels. For $k=2$ the tree is a single edge. Every such tree has $k-2$ internal vertices and $2k-3$ edges, and</p>
<div class="math-display">$$|\mathcal T_k|=(2k-5)!!,$$</div>
<p>where $(-1)!!=1$.</p>
<p><em>Proof.</em> If there are $j$ internal vertices, the degree sum gives $k+3j=2(k+j-1)$, hence $j=k-2$ and the stated edge count. For $k\geq3$, remove the leaf labelled $k$ and suppress its now degree-two neighbour. This gives a tree in $\mathcal T_{k-1}$ together with the edge on which the leaf was attached. Conversely, subdividing any edge and attaching the new leaf reverses the operation. The smaller tree has $2k-5$ edges, so $|\mathcal T_k|=(2k-5)|\mathcal T_{k-1}|$. Starting from $|\mathcal T_2|=1$ proves the formula.</p>
<p>Choose one representative of each shape and an arbitrary enumeration of its internal vertices. This enumeration is only for writing the sums below; internal vertices are not extra labelled shapes.</p>

## The multipoint inequality {#section-multipoint}

<a id="tag-AFH6" data-assertion="theorem" data-title="Multipoint tree-graph inequality on a countable bond model"></a>
<p>For $k\geq2$ and vertices $x_1,\ldots,x_k$, not necessarily distinct,</p>
<div class="math-display">$$\mathbb P(x_1,\ldots,x_k\text{ lie in one open cluster})\leq\sum_{T\in\mathcal T_k}\ \sum_{z\in V^{\operatorname{Int}(T)}}\ \prod_{\{u,v\}\in E(T)}\tau(\xi_u,\xi_v),$$</div>
<p>where $\xi_i=x_i$ at the labelled leaves and $\xi_v=z_v$ at internal vertices. The sums are nonnegative extended sums; no susceptibility or transitivity assumption is imposed.</p>
<p><em>Proof from finite-coordinate BK.</em> First allow only finitely many bonds to be open. A connection of the marked vertices has a finite open tree witness: take paths joining them, choose a spanning tree of their union, and prune branches containing no marked vertex. Attach a separate labelled pendant leaf at each occurrence of a marked vertex, assigning it the same position as that vertex and an empty path to it. This includes repeated marked vertices. Suppress all unlabelled degree-two vertices, concatenating the corresponding paths. No unlabelled leaves remain.</p>
<p>Replace each vertex of degree greater than three by a tree of degree-three vertices joining its incident branches, assigning every new vertex the old position and every inserted edge an empty path. Such a replacement can be made by successively separating two incident branches; each step reduces the remaining excess degree by one. The result is a shape in $\mathcal T_k$ with a position assigned to every vertex. Each of its edges carries an open path between its assigned endpoints. The nonempty paths have pairwise disjoint edge sets, since they partition edges of the original tree. Empty paths have empty witnesses and require no open loop.</p>
<p>For a fixed shape and internal positions, these paths witness disjoint occurrence of the $2k-3$ connection events. Finite-coordinate BK for increasing events, iterated using <a href="/tag/HP3X/">associativity of disjoint occurrence</a>, bounds this event by the product of its two-point probabilities. Finite BK is the standard probability input to this proof. A union bound over the finitely many shapes and countably many position assignments gives the result for the restricted graph.</p>
<p>Now exhaust the non-loop bonds by increasing finite sets. Every simultaneous connection has a finite path witness, so the restricted probabilities on the left increase to the full probability. Each restricted two-point factor is bounded by its full-model value, giving the same right side at every stage. Passing to the limit proves the displayed inequality.</p>
<p>For $k=2$ the bound is equality. For $k=3$ there is one shape and one branch position, giving the familiar three-point tree-graph bound. For $k=4$ there are three shapes. The construction remains valid when all marked positions coincide: every path may then be empty. It never replaces edge-disjointness by vertex-disjointness.</p>

## The three-point product inequality {#section-gladkov}

<a id="tag-87RB" data-assertion="theorem" data-title="Gladkov three-point inequality and countable finite-witness extension"></a>
<p>For independent bond percolation on a countable vertex set and any three vertices $x,y,z$,</p>
<div class="math-display">$$\mathbb P(x,y,z\text{ lie in one cluster})^2\leq8\tau(x,y)\tau(y,z)\tau(z,x).$$</div>
<p>The finite-graph theorem for distinct vertices is the cited input: Gladkov, <a href="https://arxiv.org/html/2408.08457v1#S6">Percolation Inequalities and Decision Trees</a>, arXiv:2408.08457v1, Theorem 1.1 and §6, Theorem 6.2. Its proof uses the decision-tree inequalities developed in that paper; it is not supplied by the tree-graph estimate above.</p>
<p><em>Extension from the finite theorem.</em> Exhaust the vertex set by finite sets containing the marked vertices, and close all edges outside the induced finite model. A finite complete host with zero probabilities for absent edges puts each restriction within the finite theorem. Endpoint probabilities also follow by continuity of finite-product probabilities. Every pair connection, and every simultaneous connection of the three marked vertices, has a finite collection of path witnesses. Their probabilities therefore increase to the corresponding full-model probabilities. Pass to the limit in the finite inequality. No local finiteness or susceptibility assumption is needed for this passage.</p>
<p>If two marked vertices coincide, the inequality reduces to $\tau(x,z)^2\leq8\tau(x,z)^2$ after relabelling; if all coincide it reads $1\leq8$. Thus repetitions are also allowed. This is the countable-model interpretation of S022 in the notes, with the finite cited input and the exhaustion argument distinguished.</p>

<a id="tag-5PHR" data-assertion="proposition" data-title="Independent continuations do not imply ordinary disjoint connection witnesses"></a>
<p>Two independent continuations of a stopped cluster search can both reach a target even though the underlying graph admits no edge-disjoint connections from the two previously connected marked vertices to that target.</p>
<p><em>Proof.</em> Take the path $y-x-z$. Give $xy$ probability one and $xz$ probability $q\in(0,1)$. Start at $x$, query $xy$ first, and stop on reaching $y$. Independently resample the unqueried edge $xz$ in two continuations. Both continuations reach $z$ with probability $q^2&gt;0$. But every $x$--$z$ path and every $y$--$z$ path in the original graph use the same edge $xz$. Hence ordinary disjoint occurrence of these two connections is impossible, even in the fully open configuration.</p>
<p>The two copies of $xz$ are distinct coordinates in the continuation product space. Projecting them back to a single edge destroys that distinction. The example does not contradict the three-point inequality: here its left side is $q^2$ and its right side is $8q^2$. It explains why the notes' exploration argument needs a precisely formulated decision-tree inequality and cannot be completed by claiming ordinary edge-disjointness of the two continuations. A full account of the adaptive coupling remains separate.</p>

## The four-point matching expression {#section-four-point}

<a id="tag-2GTM" data-assertion="proposition" data-title="Conditional four-point bound retains the maximum over matchings"></a>
<p>Fix four distinct marked vertices $A=\{x_1,x_2,x_3,x_4\}$ in a countable independent bond model. Write $t_{ij}=\tau(x_i,x_j)$ and $t_B$ for the probability that all vertices of $B$ lie in one cluster. Assume the four-point case of the notes' higher-order Gladkov inequality:</p>
<div class="math-display">$$t_A^2\leq108\max_{A=A_1\sqcup A_2\sqcup A_3}t_{A_1\cup A_2}t_{A_2\cup A_3}t_{A_3\cup A_1},$$</div>
<p>where the parts are nonempty. Then</p>
<div class="math-display">$$t_A^4\leq746496\left(\prod_{i&lt;j}t_{ij}\right)\max\{t_{12}t_{34},t_{13}t_{24},t_{14}t_{23}\}.$$</div>
<p>Replacing the maximum by the sum gives the symmetric sum bound in the notes. The maximum cannot in general be replaced by a single prescribed matching with a universal constant.</p>
<p><em>Proof.</em> Every partition has part sizes $1,1,2$. For singleton vertices $a,b$ and doubleton $\{c,d\}$, its product is $t_{ab}t_{acd}t_{bcd}$. Apply the <a href="/tag/87RB/">three-point inequality</a> to the last two factors and square:</p>
<div class="math-display">$$\bigl(t_{ab}t_{acd}t_{bcd}\bigr)^2\leq64t_{ab}^2t_{cd}^2t_{ac}t_{ad}t_{bc}t_{bd}=64\left(\prod_{i&lt;j}t_{ij}\right)t_{ab}t_{cd}.$$</div>
<p>Square the assumed inequality and maximize over the partitions. The unordered complementary singleton pairs produce precisely the three matchings, and $108^2\cdot64=746496$. The argument uses no division and includes zero connection probabilities.</p>
<p>To see why the maximum matters, take deterministic edges $x_1x_2$ and $x_3x_4$, and join $x_2$ to $x_3$ by a bond of probability $q\in(0,1)$, with no other edges. Then $t_A=q$, $t_{12}=t_{34}=1$, and the four cross-pair probabilities equal $q$. The product of all six probabilities is $q^4$. Choosing the prescribed matching $13|24$ would bound $q^4$ by a universal constant times $q^6$, which is impossible as $q\downarrow0$. The maximum correctly selects $12|34$. This example also satisfies the assumed higher-order inequality, whose maximal partition product is $q^2$.</p>
<p>This supplies the algebra following S023 in the <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L3524">notes</a>. A fixed partition produces a term in the maximum; it does not by itself produce a bound for the full four-point probability. The higher-order inequality with constant $108$ is an explicit input here, not a consequence of the cited three-point theorem alone.</p>

## All cluster moments {#section-moments}

<a id="tag-Y84V" data-assertion="corollary" data-title="All cluster moments under uniform finite susceptibility"></a>
<p>Write $\chi_x=\sum_y\tau(x,y)$ and suppose $M=\sup_x\chi_x&lt;\infty$. Then, for every root $o$ and integer $m\geq1$,</p>
<div class="math-display">$$\mathbb E|K_o|^m\leq(2m-3)!!\,\chi_o M^{2m-2}\leq(2m-3)!!\,M^{2m-1}.$$</div>
<p>If susceptibility has the same finite value $\chi$ at every vertex, this is the bound $(2m-3)!!\chi^{2m-1}$ of the notes. In particular, it holds in an invariant transitive model with finite susceptibility.</p>
<p><em>Proof.</em> Counting ordered tuples, with repetitions allowed, and using Tonelli gives</p>
<div class="math-display">$$\mathbb E|K_o|^m=\sum_{x_1,\ldots,x_m}\mathbb P(o,x_1,\ldots,x_m\text{ lie in one cluster}).$$</div>
<p>Apply the multipoint inequality with $k=m+1$. For each shape there are $2m-1$ edges; only the position of the leaf corresponding to $o$ is fixed. Sum successively over the position of a leaf different from this root, and delete that leaf. Its single incident factor has sum at most $M$. Continue until only the root and its neighbour remain. The last sum is $\chi_o$, so this shape contributes at most $\chi_oM^{2m-2}$. The tree count gives $(2m-3)!!$ shapes. When $m=1$ there is just the last edge and the identity is $\mathbb E|K_o|=\chi_o$.</p>
<p>Finite susceptibility at the chosen root alone is not the uniform hypothesis used in this summation. Every intermediate vertex requires a row bound. Equal susceptibilities, for example by transitivity, allow the bound to be written in terms of the single number $\chi$.</p>

## A finite root mean need not control its second moment {#section-root-counterexample}

<a id="tag-HRS7" data-assertion="proposition" data-title="A countable bond model with root susceptibility two and infinite second moment"></a>
<p>There is an independent bond model on a countable connected host graph with a root $o$ such that</p>
<div class="math-display">$$\mathbb E|K_o|=2,\qquad \mathbb E|K_o|^2=\infty.$$</div>
<p>Its root cluster is finite almost surely, but $\mathbb E e^{t|K_o|}=\infty$ for every $t&gt;0$. The susceptibilities of other vertices are not uniformly bounded.</p>
<p><em>Proof.</em> Take disjoint finite paths $C_k$, $k\geq1$, with $|C_k|=2^k$, and add one edge from $o$ to an endpoint of each path. Open every internal path edge with probability one. Independently open the edge from $o$ to $C_k$ with probability $4^{-k}$; all other pairs have probability zero. If $B_k$ is the indicator of that edge, then</p>
<div class="math-display">$$|K_o|=1+\sum_{k\geq1}2^k B_k,\qquad \mathbb E|K_o|=1+\sum_{k\geq1}2^{-k}=2.$$</div>
<p>Tonelli justifies the expectation, and its finiteness implies that $K_o$ is finite almost surely. On the other hand, $|K_o|^2\geq\sum_{k\geq1}4^kB_k$, whose expectation is infinite. Since $e^{tx}\geq t^2x^2/2$ for $x\geq0$, every positive exponential moment is infinite as well. A vertex in $C_k$ always belongs to a cluster of size at least $2^k$, so the susceptibility supremum is infinite.</p>
<p>Thus the uniform row bound in the preceding moment theorem cannot be replaced by finiteness at the chosen root. In this example the formula $\mathbb E|K_o|^2\leq\chi_o^3$ would read $\infty\leq8$. The example does not concern transitive models, where a finite root susceptibility is automatically uniform.</p>

## Dilation of a continuum multipoint limit {#section-continuum-dilation}

<a id="tag-5PBL" data-assertion="proposition" data-title="Regularly varying normalization fixes the dilation exponent"></a>
<p>For a fixed bond law on $\mathbb Z^d$ and an integer $k\geq2$, write $\tau_k(z_1,\ldots,z_k)$ for the probability that the marked vertices lie in one cluster. Let $f$ be eventually positive and regularly varying at infinity with index $\sigma\in\mathbb R$: for each $c&gt;0$, $f(c\lambda)/f(\lambda)\to c^\sigma$. Suppose the finite limit</p>
<div class="math-display">$$T_k(x_1,\ldots,x_k)=\lim_{\lambda\to\infty}f(\lambda)^k\tau_k(\lfloor\lambda x_1\rfloor,\ldots,\lfloor\lambda x_k\rfloor)$$</div>
<p>exists for every tuple of pairwise distinct points in $\mathbb R^d$, with $\lambda$ tending to infinity through positive real values and floors taken coordinatewise. Then, for every $c&gt;0$,</p>
<div class="math-display">$$T_k(cx_1,\ldots,cx_k)=c^{-k\sigma}T_k(x_1,\ldots,x_k).$$</div>
<p><em>Proof.</em> Put $s=c\lambda$. Before taking the limit, the expression defining the left side equals</p>
<div class="math-display">$$\left[\frac{f(s/c)}{f(s)}\right]^k f(s)^k\tau_k(\lfloor sx_1\rfloor,\ldots,\lfloor sx_k\rfloor).$$</div>
<p>The bracket tends to $c^{-\sigma}$ and the remaining factor to the assumed finite limit. There is no rounding error: $\lfloor\lambda(cx_i)\rfloor=\lfloor sx_i\rfloor$ exactly.</p>
<p>This proves the dilation rule in the <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L3369">notes' continuum multipoint discussion</a> once the limits and regular variation are supplied. Slowly varying factors, including logarithms, are absorbed in $f$ without changing this rule. The proposition allows the zero limit; it proves neither existence nor nontriviality. Convergence only along integer scales is a weaker hypothesis and does not justify the real reparametrization used here without further control. Translation, rotation and conformal covariance are not established by this dilation argument. The classification below assumes the full covariance law.</p>

## Two and three points under conformal covariance {#section-conformal-forms}

<a id="tag-N76U" data-assertion="theorem" data-title="Mobius covariance determines two- and three-point functions"></a>
<p>Let $d\geq2$ and $\sigma\in\mathbb R$. For $k=2,3$, let $T_k$ be a finite nonnegative function on ordered tuples of $k$ distinct points in $\mathbb R^d$. Suppose that for every Mobius transformation $\phi$, whenever the marked points and their images are finite,</p>
<div class="math-display">$$T_k(\phi(x_1),\ldots,\phi(x_k))=\left(\prod_{i=1}^k\lambda_\phi(x_i)^{-\sigma}\right)T_k(x_1,\ldots,x_k),$$</div>
<p>where $\lambda_\phi(x)&gt;0$ is the local length-scaling factor. Here the Mobius group is generated by Euclidean similarities, including reflections, and sphere inversions, acting on the one-point compactification. Then there are constants $C_2,C_3\geq0$ such that</p>
<div class="math-display">$$T_2(x_1,x_2)=C_2\|x_1-x_2\|^{-2\sigma},\qquad T_3(x_1,x_2,x_3)=C_3\prod_{1\leq i&lt;j\leq3}\|x_i-x_j\|^{-\sigma}.$$</div>
<p>No continuity, permutation symmetry or strict positivity of $T_k$ is assumed. If, in addition,</p>
<div class="math-display">$$T_3(x,y,z)^2\leq8T_2(x,y)T_2(y,z)T_2(z,x)$$</div>
<p>for all distinct triples, then $C_3^2\leq8C_2^3$.</p>
<p><em>Proof.</em> The Mobius distance identity is</p>
<div class="math-display">$$\|\phi(x)-\phi(y)\|=\lambda_\phi(x)^{1/2}\lambda_\phi(y)^{1/2}\|x-y\|.$$</div>
<p>It follows by direct calculation for similarities and inversions and then by composition. If an intermediate image is infinite, approximate the finite endpoints by points avoiding the finitely many intermediate poles and pass to the limit in this identity. The final map is smooth with positive length factor at the endpoints under consideration. This argument concerns the map and the distance identity; it assumes no continuity of $T_k$.</p>
<p>The covariance factors therefore cancel in</p>
<div class="math-display">$$R_2(x,y)=T_2(x,y)\|x-y\|^{2\sigma},\qquad R_3(x,y,z)=T_3(x,y,z)\bigl(\|x-y\|\|y-z\|\|z-x\|\bigr)^\sigma.$$</div>
<p>Similarities act transitively on ordered pairs of distinct points, so $R_2$ is constant. To see the corresponding fact for triples, take two ordered triples $(x_1,x_2,x_3)$ and $(y_1,y_2,y_3)$. Write</p>
<div class="math-display">$$I_a(z)=\frac{z-a}{\|z-a\|^2},\qquad I_a(a)=\infty,\qquad I_a(\infty)=0.$$</div>
<p>A similarity $S$ sends the ordered pair $(I_{x_3}(x_1),I_{x_3}(x_2))$ to $(I_{y_3}(y_1),I_{y_3}(y_2))$. Hence the single Mobius transformation $\phi=I_{y_3}^{-1}\circ S\circ I_{x_3}$ sends each $x_i$ to $y_i$. Its final images are finite, including $\phi(x_3)=y_3$. If $S(z)=cUz+v$, direct expansion near $x_3$ gives $\phi(x_3+h)=y_3+c^{-1}Uh+O(\|h\|^2)$, so the length factor there is $c^{-1}&gt;0$. The assumed covariance therefore applies to this map. We never evaluate $T_3$ at an infinite point. Thus $R_3$ is constant as well, proving both formulas. Substitution into the additional inequality cancels the positive product of distance powers and gives $C_3^2\leq8C_2^3$.</p>
<p>The additional inequality holds, in particular, if $T_2$ and $T_3$ are finite continuum limits with the same positive normalization $f$: multiply the discrete <a href="/tag/87RB/">Gladkov inequality</a> by $f(\lambda)^6$ and pass to the limit at a fixed distinct triple, whose lattice approximations are distinct for all sufficiently large scales. This implication uses the cited finite three-point theorem through 87RB; the classification of covariant functions does not. The zero three-point limit is allowed.</p>
<p>This proves the conditional two- and three-point classification in the <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L3401">notes' continuum discussion</a>. It does not establish existence, nontriviality or conformal covariance of a percolation limit. For four points, the ratio $\|x_1-x_2\|\|x_3-x_4\|/(\|x_1-x_3\|\|x_2-x_4\|)$ is unchanged by the distance identity and takes different values on different configurations. The group is consequently not transitive on ordered quadruples, so the same constancy argument no longer applies.</p>

## Recursive distance geometry {#section-recursive-geometry}

<a id="tag-Y4H4" data-assertion="definition" data-title="Recursive three-part distance quantity"></a>
<p>For a finite set $A\subset\mathbb R^d$ of at least two distinct points, define $S(A)$ recursively by</p>
<div class="math-display">$$S(\{x,y\})=\|x-y\|_2^2,\qquad S(A)=\min_{A=A_1\sqcup A_2\sqcup A_3}\sqrt{S(A_1\cup A_2)S(A_2\cup A_3)S(A_3\cup A_1)}\quad(|A|\geq3),$$</div>
<p>where all three parts are nonempty. Each pairwise union has between two and $|A|-1$ points, so the recursion terminates. There are finitely many partitions and every base distance is positive; consequently $0&lt;S(A)&lt;\infty$ and the minimum is attained. No value on singletons is needed.</p>

<a id="tag-9YE6" data-assertion="proposition" data-title="Explicit small-set formulas and covariance of the recursive distance quantity"></a>
<p>For three points, $S(\{x,y,z\})=\|x-y\|_2\|y-z\|_2\|z-x\|_2$. For four points $A=\{a,b,c,d\}$, it is the minimum over the three unordered pairings of the expressions</p>
<div class="math-display">$$\|a-b\|_2\|c-d\|_2\sqrt{\|a-c\|_2\|a-d\|_2\|b-c\|_2\|b-d\|_2}.$$</div>
<p>More generally, suppose $\phi$ is injective on $A$ and positive numbers $\lambda(x)$ satisfy</p>
<div class="math-display">$$\|\phi(x)-\phi(y)\|_2^2=\lambda(x)\lambda(y)\|x-y\|_2^2\qquad(x,y\in A).$$</div>
<p>Then $S(\phi(A))=S(A)\prod_{x\in A}\lambda(x)$. In particular, for a similarity $\phi(x)=cUx+v$ with $c&gt;0$ and orthogonal $U$, one has $S(\phi(A))=c^{|A|}S(A)$.</p>
<p><em>Proof.</em> A three-point partition consists of three singletons. For four points every partition has sizes $1,1,2$; insert the three-point formula into the recursion to obtain the displayed pairing term. Interchanging the singleton pair and its complement leaves that term unchanged, giving precisely three possibilities.</p>
<p>The covariance identity holds for two points by assumption. Suppose it holds for all proper subsets of $A$ of size at least two. In any three-part partition, each point belongs to exactly two pairwise unions. The product of their three covariance factors is therefore $\prod_{x\in A}\lambda(x)^2$. Its square root is independent of the partition, so it factors out of the minimum. Injectivity makes partitions of $A$ correspond bijectively to partitions of $\phi(A)$, completing the induction. For a similarity take $\lambda(x)=c$.</p>
<p>Inversion $\phi(x)=x/\|x\|_2^2$ on nonzero points satisfies the same distance identity with $\lambda(x)=\|x\|_2^{-2}$, as direct expansion of the squared distance shows. The identity is preserved under composition, multiplying the factors at successive images. Thus the covariance also applies to compositions of similarities and inversions whenever all points and images are finite and avoid the relevant poles. This is a property of $S$, not a claim of conformal covariance for percolation probabilities.</p>

<a id="tag-C4A5" data-assertion="proposition" data-title="Higher-point product inequalities imply the recursive geometric bound"></a>
<p>Let $A\subset\mathbb R^d$ be finite, $n=|A|\geq2$, and let $t(B)\geq0$ be specified for every subset $B\subseteq A$ with at least two points. Suppose $\sigma,C_2&gt;0$ and constants $K_m&gt;0$, $3\leq m\leq n$, satisfy</p>
<div class="math-display">$$t(\{x,y\})\leq C_2\|x-y\|_2^{-2\sigma},\qquad t(B)^2\leq K_{|B|}\max_{B=B_1\sqcup B_2\sqcup B_3}\prod_{i&lt;j}t(B_i\cup B_j)\quad(|B|\geq3),$$</div>
<p>with nonempty parts. Set $D_2=C_2$ and recursively</p>
<div class="math-display">$$D_m=\left[K_m\max_{\substack{a,b,c\geq1\\a+b+c=m}}D_{a+b}D_{b+c}D_{c+a}\right]^{1/2}.$$</div>
<p>Then $t(A)\leq D_n S(A)^{-\sigma}$.</p>
<p><em>Proof.</em> The pair case is the assumed bound. At each larger set, apply induction to the three proper pairwise unions. Their constants are bounded by the maximum in $D_m$, while their distance factors obey</p>
<div class="math-display">$$\max_{B=B_1\sqcup B_2\sqcup B_3}\left[\prod_{i&lt;j}S(B_i\cup B_j)\right]^{-\sigma/2}=S(B)^{-\sigma}.$$</div>
<p>This identity uses $\sigma&gt;0$: taking a negative power turns the maximum into the minimum defining $S$. Taking the square root of the product inequality completes the induction. All constants depend only on the cardinality and the given input constants.</p>
<p>For connection probabilities, the notes' higher-order Gladkov input has $K_m=4(m-1)^2(2^{m-2}-1)$. With a two-point estimate of exponent $d-2+\eta&gt;0$, take $2\sigma=d-2+\eta$. The proposition gives the stated recursive bound once those inputs hold. This covers the recursion and covariance in the <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L3644">notes</a>; it proves neither the higher-order probability inequality nor the separate comparison with arborescence sweep products or planar RSW lower bounds.</p>

## Comparing the recursion with sweep trees {#section-sweep}

<a id="tag-CS13" data-assertion="definition" data-title="Sweep product on a finite metric space"></a>
<p>Let $(A,d)$ be a finite metric space with $n\geq2$. Use the recursion of <a href="/tag/Y4H4/">Y4H4</a> with pair values $d(x,y)^2$ to define $S_d(A)$. For a tree on $A$ directed toward a root, let $A_x$ consist of $x$, its parent and all its descendants when $x$ is not the root; set $A_{\rm root}=A$. Define</p>
<div class="math-display">$$\operatorname{Sweep}_d(A)=\min_T\prod_{x\in A}\operatorname{diam}_d(A_x),$$</div>
<p>where the minimum ranges over all rooted trees on $A$. The root factor is included. Both quantities are positive, are nondecreasing in each distance, and multiply by $c^n$ when every distance is multiplied by $c&gt;0$. For $S_d$ these facts follow by induction through the recursion; for the sweep product they hold for every tree before taking the minimum.</p>

<a id="tag-ESZG" data-assertion="theorem" data-title="Exact recursive and sweep products for an ultrametric"></a>
<p>Suppose $d$ is an ultrametric on $A$, meaning $d(x,z)\leq\max\{d(x,y),d(y,z)\}$. If $T$ is a spanning tree of minimum edge-length product, then</p>
<div class="math-display">$$S_d(A)=\operatorname{Sweep}_d(A)=\operatorname{diam}_d(A)\prod_{e\in T}d(e).$$</div>
<p><em>Proof.</em> Denote the expression on the right by $U(A)$. For any subset $B$ of at least two points, let $c_t(B)$ count its equivalence classes under $d(x,y)\leq t$. Kruskal's construction joins each such class internally before using larger edges, so its minimum-product spanning tree has $|B|-c_t(B)$ edges of length at most $t$. Minimum-product optimality follows by the usual exchange argument: replacing a longer edge by a shorter edge across its cut decreases the product. Put $f(1)=0$ and $f(k)=k$ for $k\geq2$. For $R=\operatorname{diam}(A)$, integrating the logarithms of the tree edges and the extra diameter factor gives</p>
<div class="math-display">$$\log U(B)=|B|\log R-\int_0^R\bigl(|B|-f(c_t(B))\bigr)\,\frac{dt}{t}.$$</div>
<p>The integrand vanishes below the smallest positive distance in $B$. The extra subtraction when $c_t(B)=1$ accounts for the diameter factor.</p>
<p>Fix a three-part partition of $A$ and $0&lt;t&lt;R$, so $c=c_t(A)\geq2$. Each $t$-class meets either one part, contributing two to the sum of the three union class counts, or several parts, contributing three. Thus that sum is $2c+h$, where $h$ counts classes meeting several parts. At most one pairwise union can have only one class: two such unions would force all of $A$ into one class. If there is one, its class meets two parts, so $h\geq1$. Consequently</p>
<div class="math-display">$$\sum_{i&lt;j}f(c_t(A_i\cup A_j))\geq2c_t(A).$$</div>
<p>Insert this inequality into the integral formula to get $U(A)\leq\sqrt{\prod_{i&lt;j}U(A_i\cup A_j)}$.</p>
<p>When $|A|\geq3$, a partition attaining equality can be chosen simultaneously at every threshold. Consider the maximal blocks of diameter less than $R$. If there are at least three, divide whole blocks into three nonempty groups. Every smaller threshold class lies in one part, and each pairwise union meets at least two maximal blocks, so equality holds. If there are exactly two maximal blocks, one has at least two points. Split that block into two groups of its own maximal subblocks, and use the other block as the third part. Below the first block's diameter, each class lies in one part. Above that diameter and below $R$, exactly one class meets two parts and exactly one pairwise union has one class. Again equality holds. Since $U$ agrees with $d^2$ on pairs, induction now gives $S_d=U$.</p>
<p>For any rooted tree, each nonroot set $A_x$ contains its parent edge. Its sweep product is therefore at least $\operatorname{diam}(A)$ times the product of its edge lengths, hence at least $U(A)$. To attain this bound, choose a root in one maximal ultrametric block, construct such trees recursively inside all blocks, and attach the root of every other block directly to the chosen root. Every nonroot descendant set together with its parent has diameter exactly the length of its parent edge. The connecting edges have length $R$, and the resulting edge product is minimal by the same block decomposition. Its sweep product is $U(A)$.</p>

<a id="tag-WDGK" data-assertion="theorem" data-title="Recursive and sweep geometry are comparable with explicit cardinality constants"></a>
<p>For every finite metric space $(A,d)$ with $n\geq2$,</p>
<div class="math-display">$$(n-1)^{-n}\operatorname{Sweep}_d(A)\leq S_d(A)\leq(n-1)^n\operatorname{Sweep}_d(A).$$</div>
<p><em>Proof.</em> Take a minimum-product spanning tree $T$ for $d$, set $u(x,x)=0$, and for distinct $x,y$ let $u(x,y)$ be the largest edge length on its unique $x$--$y$ path. This is an ultrametric: the $x$--$z$ path is contained in the union of the $x$--$y$ and $y$--$z$ paths. Also $u(x,y)\leq d(x,y)$, since otherwise replacing a largest path edge by $xy$ would decrease the tree product. The triangle inequality along the path gives the reverse comparison</p>
<div class="math-display">$$u(x,y)\leq d(x,y)\leq(n-1)u(x,y).$$</div>
<p>Monotonicity and degree-$n$ homogeneity place both $S_d(A)$ and $\operatorname{Sweep}_d(A)$ between $S_u(A)=\operatorname{Sweep}_u(A)$ and $(n-1)^n$ times that common value. Comparing the two intervals gives the result.</p>
<p>This proves the fixed-cardinality sweep comparison in the <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L3696">notes</a> by ultrametric reduction. It includes the two-point case exactly and retains the root factor in the sweep definition. The comparison is deterministic; it supplies neither the higher-order percolation inequality nor an RSW gluing argument.</p>

## Planar arm-and-circuit gluing {#section-planar-gluing}

<a id="tag-FAT3" data-assertion="theorem" data-title="A planar multipoint lower bound from circuit and two-point inputs"></a>
<p>Consider homogeneous nearest-neighbour bond percolation on $\mathbb Z^2$. Write $B_r(x)=x+[-r,r]^2$ for the lattice box. Suppose $a,c,s&gt;0$ satisfy:</p>
<ul><li>$\tau(x,y)\geq a\|x-y\|_2^{-2s}$ for distinct lattice vertices;</li><li>for every integer $r\geq1$, the probability of an open simple circuit contained in $B_{4r}(0)\setminus B_{2r}(0)$ and surrounding $B_{2r}(0)$ is at least $c$.</li></ul>
<p>Then every set $A$ of $k\geq2$ distinct lattice vertices satisfies</p>
<div class="math-display">$$\mathbb P(A\text{ lies in one cluster})\geq\bigl(c\sqrt a\,48^{-s}\bigr)^k\operatorname{Sweep}(A)^{-s},$$</div>
<p>where sweep diameters use Euclidean distance. If the two-point upper bound and higher-point product hypotheses of <a href="/tag/C4A5/">C4A5</a> also hold with exponent $s$, then the connection probability is comparable, with fixed-cardinality constants, to both $S(A)^{-s}$ and $\operatorname{Sweep}(A)^{-s}$.</p>
<p><em>Proof.</em> Let $\pi(r)$ be the probability of an arm from zero to the vertex boundary of $B_r(0)$, using edges inside the box. The event $0\leftrightarrow3re_1$ forces an arm inside each of the disjoint boxes $B_r(0)$ and $B_r(3re_1)$. Those arm events depend on disjoint edge coordinates and have the same probability. Thus, for integer $r\geq1$,</p>
<div class="math-display">$$\pi(r)^2\geq\tau(0,3re_1)\geq a(3r)^{-2s},\qquad\pi(r)\geq\sqrt a\,(3r)^{-s}.$$</div>
<p>Choose a rooted tree attaining the sweep minimum, deterministically from the marked points. Put $R_x=\operatorname{diam}(A_x)$ and $r_x=\lceil R_x\rceil$. Distinct lattice points give $R_x\geq1$, so $r_x\leq2R_x$. If $y$ has parent $x$, then $A_y\subseteq A_x$, hence $r_y\leq r_x$, and $\|x-y\|_\infty\leq R_y\leq r_y$.</p>
<p>For each marked point $x$, require an arm from $x$ to $\partial B_{8r_x}(x)$ and an open circuit in $B_{4r_x}(x)\setminus B_{2r_x}(x)$ surrounding the inner box. All these events are increasing. Harris association and the two hypotheses give their joint probability at least</p>
<div class="math-display">$$\prod_{x\in A}c\pi(8r_x)\geq\prod_{x\in A}c\sqrt a\,(24r_x)^{-s}\geq\bigl(c\sqrt a\,48^{-s}\bigr)^k\prod_{x\in A}R_x^{-s}.$$</div>
<p>No independence between the arms and circuits is assumed.</p>
<p>It remains to check the deterministic gluing. For a child $y$ with parent $x$, both vertices are inside the inner box surrounded by the circuit at $y$. The arm from $y$ exits its outer box. The endpoint $v$ of the parent's arm also lies outside that outer box, since</p>
<div class="math-display">$$\|v-y\|_\infty\geq8r_x-\|x-y\|_\infty\geq8r_x-r_y\geq7r_y&gt;4r_y.$$</div>
<p>Each arm therefore crosses the child's circuit. In the planar nearest-neighbour embedding such crossings share lattice vertices, so the two arms are connected through the open circuit. This joins every child to its parent, and hence all marked points. The product of the $R_x$ is the sweep minimum, proving the lower bound. The conditional upper bound is C4A5; <a href="/tag/WDGK/">the deterministic sweep comparison</a> identifies the two geometric quantities up to constants.</p>
<p>This supplies the gluing argument for S024 in the <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L3778">notes</a>, with integer radii and the crossing geometry explicit. At $p=1/2$, the uniform circuit lower bound is the RSW input, which is not proved here. The two-point power law and higher-order product inequalities likewise remain hypotheses where used. Only a lower arm estimate is needed, and the two-disjoint-box argument supplies it without a full two-point/one-arm comparison theorem.</p>

## Growth from a revealed cluster {#section-cluster-extension}

<a id="tag-F4RR" data-assertion="proposition" data-title="An independent added layer bounds growth conditional on the original cluster"></a>
<p>Let $\omega$ and $\xi$ be independent bond configurations on a countable vertex set. Write $C=K_o(\omega)$ and $K_o^+=K_o(\omega\cup\xi)$. Suppose the union law has uniformly bounded susceptibility $\sup_v\mathbb E|K_v^+|\leq\chi_+&lt;\infty$, and the added-edge probabilities satisfy</p>
<div class="math-display">$$\sup_u\sum_{v\ne u}\mathbb P(\{u,v\}\in\xi)\leq\varepsilon&lt;\infty.$$</div>
<p>Then almost surely</p>
<div class="math-display">$$\mathbb E\bigl[|K_o^+|\mid C\bigr]\leq(1+\varepsilon\chi_+)|C|.$$</div>
<p>In particular, for every nonnegative function $f$ of the original cluster,</p>
<div class="math-display">$$\mathbb E\bigl[|K_o^+|f(C)\bigr]\leq(1+\varepsilon\chi_+)\mathbb E\bigl[|C|f(C)\bigr],$$</div>
<p>with extended expectations allowed.</p>
<p><em>Proof.</em> The cluster $C$ is finite almost surely. Conditional on $C=S$, all original boundary bonds are closed, while original bonds with both endpoints outside $S$ keep their independent law. No added bond has been revealed. If $x\in K_o^+\setminus S$, take a finite open path to $x$ and its last exit from $S$. That exit uses an added bond $\{u,v\}$, with $u\in S$ and $v\notin S$, followed by a path lying entirely outside $S$. Its added bond is independent of the outside configuration. The expected size of the outside union cluster at $v$ is at most $\chi_+$ by domination by the full union law. Summing over $x,u,v$ gives</p>
<div class="math-display">$$\mathbb E\bigl[|K_o^+|\mid C=S\bigr]\leq |S|+\sum_{u\in S}\sum_{v\notin S}\mathbb P(\{u,v\}\in\xi)\chi_+\leq(1+\varepsilon\chi_+)|S|.$$</div>
<p>Tonelli justifies the sums. Multiplication by $f(S)$ and averaging proves the last assertion. The last-exit choice is useful here: the remaining path uses no revealed boundary bond, even if the original path left and re-entered $S$ several times.</p>

## Mass at one scale and at smaller scales {#section-multiscale-mass}

<a id="tag-D6CQ" data-assertion="proposition" data-title="Localized moments and mesoscopic negligibility supply the mass events for gluing"></a>
<p>Let $K^{(r)}$ be random sets containing a root $o$ in a countable metric space, for $r\geq1$. Put $X_r=|K^{(r)}|$, $Y_{r,\lambda}=|K^{(r)}\cap B_{\lambda r}(o)|$, and $m_q(r)=\mathbb E X_r^q$. Fix $0&lt;\alpha&lt;\theta$. Assume positive constants $C_1,c_2,C_3$ satisfy</p>
<div class="math-display">$$m_1(r)\leq C_1r^\alpha,\qquad m_2(r)\geq c_2r^{\alpha+\theta},\qquad m_3(r)\leq C_3r^{\alpha+2\theta}.$$</div>
<p>Assume the first two moments localize: for every $\eta&gt;0$ a single $\lambda\geq1$ gives $m_q(r)\leq(1+\eta)\mathbb E Y_{r,\lambda}^q$ for $q=1,2$ and every $r\geq1$. Assume also <a href="/tag/QMN5/">mesoscopic negligibility</a> at scale $r^\theta$. Then there are fixed $a,b&gt;0$ and $\lambda_0\geq1$ such that</p>
<div class="math-display">$$\mathbb P(Y_{r,\lambda_0}\geq ar^\theta)\geq br^{\alpha-\theta}\qquad(r\geq1).$$</div>
<p>Moreover, for each $\eta&gt;0$ there are $\delta&gt;0$ and $\lambda\geq1$ such that</p>
<div class="math-display">$$\mathbb E\bigl[X_r;Y_{r,\lambda}\leq\delta r^\theta\bigr]\leq\eta r^\alpha\qquad(r\geq1).$$</div>
<p><em>Proof.</em> Choose $\lambda_0$ with $\mathbb E Y_{r,\lambda_0}^2\geq m_2(r)/2$, and set $a=c_2/(4C_1)$. Writing $Y=Y_{r,\lambda_0}$, the contribution of $Y&lt;ar^\theta$ to its second moment is at most $ar^\theta\mathbb E Y\leq c_2r^{\alpha+\theta}/4$. Hence Hölder's inequality gives</p>
<div class="math-display">$$\frac{c_2}{4}r^{\alpha+\theta}\leq\mathbb E[Y^2;Y\geq ar^\theta]\leq(\mathbb E Y^3)^{2/3}\mathbb P(Y\geq ar^\theta)^{1/3}.$$</div>
<p>Cubing and using $\mathbb E Y^3\leq m_3(r)$ proves the probability bound, for example with $b=(c_2/4)^3/C_3^2$.</p>
<p>For the second assertion, choose $\lambda$ so that $\mathbb E(X_r-Y_{r,\lambda})\leq\eta r^\alpha/2$ uniformly. For every $h&gt;0$,</p>
<div class="math-display">$$X_r\mathbf1_{\{Y_{r,\lambda}\leq h\}}\leq X_r-Y_{r,\lambda}+(X_r\wedge h).$$</div>
<p>Mesoscopic negligibility and the mean upper bound give a $\delta&gt;0$ for which $\mathbb E(X_r\wedge\delta r^\theta)\leq\eta r^\alpha/2$ at all sufficiently large radii, say $r\geq r_0$. Decrease $\delta$ further until $\delta r_0^\theta&lt;1$. At $1\leq r&lt;r_0$ the bad event is empty, since $Y_{r,\lambda}\geq1$. This extends the estimate to every radius without interchanging the two limits in mesoscopic negligibility.</p>

<a id="tag-JC24" data-assertion="proposition" data-title="Large-scale local mass makes small-scale local mass conditionally likely"></a>
<p>Consider a translation-invariant increasing family of independent bond laws on $\mathbb Z^d$, coupled by independent Poisson edge increments. Suppose $\chi_R\leq C R^\alpha$ and, for $1\leq r\leq R$, the added layer from $r$ to $R$ has off-diagonal probability row at most $C r^{-\alpha}$. Let $0&lt;\alpha&lt;\theta$. Suppose fixed $a,b&gt;0$, $\lambda_0\geq1$ give events</p>
<div class="math-display">$$E_R=\{|K_o^{(R)}\cap B_{\lambda_0R}(o)|\geq aR^\theta\},\qquad\mathbb P(E_R)\geq bR^{\alpha-\theta},$$</div>
<p>and suppose the localized small-mass estimate in <a href="/tag/D6CQ/">D6CQ</a> holds for every $\eta&gt;0$. Then for every $\varepsilon&gt;0$ there exist $\delta&gt;0$ and $\lambda\geq1$ such that, simultaneously for all $1\leq r\leq R$,</p>
<div class="math-display">$$\mathbb P\bigl(|K_o^{(r)}\cap B_{\lambda r}(o)|\leq\delta r^\theta\mid E_R\bigr)\leq\varepsilon.$$</div>
<p><em>Proof.</em> Write $D_r$ for the event being conditioned against. It depends only on the smaller cluster. The <a href="/tag/F4RR/">cluster-extension bound</a> gives</p>
<div class="math-display">$$\mathbb E[|K_o^{(R)}|;D_r]\leq(1+C^2r^{-\alpha}R^\alpha)\eta r^\alpha\leq(1+C^2)\eta R^\alpha.$$</div>
<p>On $E_R$, the larger cluster has at least $aR^\theta$ vertices. Therefore</p>
<div class="math-display">$$\mathbb P(D_r\mid E_R)\leq\frac{\mathbb E[|K_o^{(R)}|;D_r]}{aR^\theta\mathbb P(E_R)}\leq\frac{(1+C^2)\eta}{ab}.$$</div>
<p>Choose $\eta\leq\varepsilon ab/(1+C^2)$. The constants $a,b$ of the conditioning event stay fixed while its conditional error is made arbitrarily small.</p>

## Joining at separated scales {#section-long-range-gluing}

<a id="tag-L5IG" data-assertion="theorem" data-title="Multiscale local mass and fresh edges imply a sweep lower bound"></a>
<p>Let $d\geq1$, $0&lt;\alpha&lt;d$, $\theta=(d+\alpha)/2$ and $s=\theta-\alpha$. Consider a translation-invariant bond process $(\omega_r)_{r\geq1}$ on $\mathbb Z^d$, with independent Poisson increments on each unordered non-loop edge, and let $\omega_\infty=\bigcup_r\omega_r$. Suppose the events $E_R$ and the uniform conditional conclusion of <a href="/tag/JC24/">JC24</a> hold. Suppose also that for every $D\geq1$ there is $c_D&gt;0$ such that the added Poisson intensity between radii $r$ and $2Dr$ on each edge of length at most $Dr$ is at least $c_Dr^{-d-\alpha}$, uniformly for $r\geq1$. Then for every integer $n\geq2$ there is $c_n&gt;0$ such that every set $A$ of $n$ distinct lattice vertices satisfies</p>
<div class="math-display">$$\mathbb P(A\text{ lies in one cluster of }\omega_\infty)\geq c_n\operatorname{Sweep}(A)^{-s}.$$</div>
<p>Diameters and balls use Euclidean distance. Constants may depend on $n$ and the stated uniform inputs, but not on the positions of the marked vertices.</p>
<p><em>Proof.</em> Choose a rooted tree attaining the <a href="/tag/CS13/">sweep minimum</a>. Enumerate its vertices $a_1,\ldots,a_n$ so that $R_i=\operatorname{diam}(A_{a_i})$ is nondecreasing and every parent has larger index than its child. This is possible because $A_x\subseteq A_{\operatorname{parent}(x)}$; break equal-radius ties with children first. The root is $a_n$, and each $R_i\geq1$.</p>
<p>Apply conditional persistence with $\varepsilon=1/(2n)$, obtaining $\delta,\lambda$. Set $D=2\lambda+1$, $L=2D$, and $r_i=L^iR_i$. Thus $r_{i+1}\geq Lr_i$. For each $j$, let $F_j$ require</p>
<div class="math-display">$$|K_{a_j}^{(r_i)}\cap B_{\lambda r_i}(a_j)|&gt;\delta r_i^\theta\qquad(1\leq i\leq j).$$</div>
<p>Conditional on the translated event $E_{r_j}$, a union bound over its $j$ scales gives $\mathbb P(F_j\mid E_{r_j})\geq1-j/(2n)\geq1/2$. Consequently $\mathbb P(F_j)\geq(b/2)r_j^{-s}$. All $F_j$ are increasing in the Poisson coordinates, so Harris association gives</p>
<div class="math-display">$$\mathbb P\left(\bigcap_{j=1}^nF_j\right)\geq(b/2)^n\prod_{j=1}^nr_j^{-s}.$$</div>
<p>Reorder the same requirements by scale. Let $A_i$ require the local-mass bound at radius $r_i$ for every $a_j$ with $j\geq i$, so that $\mathcal A=\bigcap_i A_i=\bigcap_jF_j$. Let $\mathcal F_i$ reveal all increments up to $r_i$. For $i&lt;n$, write $\sigma(i)&gt;i$ for the parent index and let $G_i$ be the event that $a_i$ and $a_{\sigma(i)}$ are connected by radius $Lr_i$.</p>
<p>On $A_i$, both clusters have more than $\delta r_i^\theta$ vertices in their respective $\lambda r_i$ balls. If the clusters already agree, $G_i$ holds. Otherwise these two sets are disjoint, and every edge between them has length at most</p>
<div class="math-display">$$2\lambda r_i+|a_i-a_{\sigma(i)}|\leq(2\lambda+1)r_i=Dr_i.$$</div>
<p>The fresh increments on these edges are independent given $\mathcal F_i$. Since $2\theta=d+\alpha$, the conditional probability that at least one appears by $Lr_i$ is at least $q=1-\exp(-c_D\delta^2)&gt;0$. Hence $\mathbb P(G_i\mid\mathcal F_i)\geq q\mathbf1_{A_i}$.</p>
<p>The later mass events and $G_i$ are increasing in the unexposed independent increments. Conditional Harris therefore implies</p>
<div class="math-display">$$\mathbb P\left(G_i\cap\bigcap_{j&gt;i}A_j\mid\mathcal F_i\right)\geq q\mathbf1_{A_i}\mathbb P\left(\bigcap_{j&gt;i}A_j\mid\mathcal F_i\right).$$</div>
<p>Every earlier $G_j$ is $\mathcal F_i$-measurable because $Lr_j\leq r_i$. Multiply by $\mathbf1_{\cap_{j\leq i}A_j\cap\cap_{j&lt;i}G_j}$ and average. This gives the correctly indexed recurrence</p>
<div class="math-display">$$\mathbb P\left(\mathcal A\cap\bigcap_{j\leq i}G_j\right)\geq q\mathbb P\left(\mathcal A\cap\bigcap_{j&lt;i}G_j\right).$$</div>
<p>After $n-1$ steps, all tree links hold with probability at least $q^{n-1}\mathbb P(\mathcal A)$. They connect all marked vertices in $\omega_\infty$. Finally,</p>
<div class="math-display">$$\prod_{i=1}^nr_i^{-s}=L^{-s n(n+1)/2}\prod_{i=1}^nR_i^{-s}=L^{-s n(n+1)/2}\operatorname{Sweep}(A)^{-s}.$$</div>
<p>This proves the claim with $c_n=q^{n-1}(b/2)^nL^{-s n(n+1)/2}$. No independence between the mass events and the joining events was used. Conditional association is applied only after revealing the earlier increments.</p>

<a id="tag-2BBE" data-assertion="corollary" data-title="The power-law cutoff criterion yields the long-range multipoint lower bound"></a>
<p>Under the hypotheses of the <a href="/tag/YJ5E/">power-law cutoff criterion</a>, with $d/3&lt;\alpha&lt;d$, let $\tau_\beta(A)$ denote the full-model connection probability of a finite marked set $A\subset\mathbb Z^d$. For every fixed $n\geq2$,</p>
<div class="math-display">$$\tau_\beta(A)\succeq_n\operatorname{Sweep}(A)^{-(d-\alpha)/2}\asymp_n S(A)^{-(d-\alpha)/2}\qquad(|A|=n).$$</div>
<p>If the pair upper bound and higher-point product inequalities in <a href="/tag/C4A5/">C4A5</a> also hold with $\sigma=(d-\alpha)/2$, then $\tau_\beta(A)\asymp_n S(A)^{-(d-\alpha)/2}$. The first conclusion requires no pointwise two-point lower bound.</p>
<p><em>Proof.</em> The cutoff criterion gives $m_q(r)\asymp r^{\alpha+(q-1)\theta}$ for $q=1,2,3$, where $\theta=(d+\alpha)/2$, and mesoscopic negligibility. Its localization hypothesis includes the first two moments. These moment comparisons, initially stated for large $r$, extend to $r\geq1$ by adjusting constants: the cluster contains its root and is dominated on any bounded radius interval by the cluster at the interval's upper endpoint. Thus D6CQ supplies both local-mass estimates.</p>
<p>Couple the soft cutoffs by independent Poisson processes on the edges. The <a href="/tag/C4E9/">omitted-intensity row bound</a> bounds the added probability row from $r$ to $R$ by $Cr^{-\alpha}$. Together with $\chi_R\preceq R^\alpha$, this verifies JC24. For $p=d+\alpha$, an edge of length $\ell\leq Dr$ receives between $r$ and $2Dr$ the intensity</p>
<div class="math-display">$$\beta A\left[\bigl(\ell^{-p}-(2Dr)^{-p}\bigr)_+-\bigl(\ell^{-p}-r^{-p}\bigr)_+\right]\geq\beta A\bigl(D^{-p}-(2D)^{-p}\bigr)r^{-p}.$$</div>
<p>For $\ell\leq r$ subtract the two powers of the cutoff radii; for $r&lt;\ell\leq Dr$ the second positive part vanishes. The coefficient is positive. L5IG now gives the lower bound, and <a href="/tag/WDGK/">the sweep comparison</a> replaces sweep by $S$. C4A5 supplies the stated conditional upper bound.</p>
<p>This completes a conditional route to S045 of the <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L6202">notes</a>. The assumptions of YJ5E—cutoff susceptibility order, weak localization and rooted damping—remain explicit. A two-point estimate alone is not the input to the lower-bound argument supplied here. For the more general kernels of <a href="https://arxiv.org/html/2508.18808v1">Critical LRP II</a>, Proposition II.5.9 uses the paper's weak-localization theory, and Lemma II.5.11 supplies the corresponding scale-persistence step. The argument above isolates those mechanisms with fixed conditioning thresholds and separated joining radii; it does not identify the full set of kernels satisfying the paper's localization hypotheses.</p>

## Source scope {#section-source}

<p>This supplies the general combinatorial and summation arguments in the preliminary notes, Chapter 4, lines 1287–1347 (S006). The finite-coordinate BK inequality is the input; the refinement into trivalent shapes, repeated-vertex convention and shape count are given explicitly here. The <a href="/tag/XLWI/">exponential-moment consequence</a> retains the root mean and the uniform susceptibility scale separately. Identifying finite susceptibility with the whole subcritical phase is a separate sharpness theorem.</p>

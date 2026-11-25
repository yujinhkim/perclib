---
{
  "id": "bk-inequality",
  "title": "The van den Berg–Kesten inequality",
  "subtitle": "Disjoint witnesses under independent percolation",
  "kind": "theorem",
  "category": "Inequalities",
  "summary": "Finite-coordinate BK follows from a coordinate induction and independent bit blocks. Finite open witnesses extend it to countably many coordinates and repeated disjoint occurrence.",
  "context": ["Configurations are subsets of a coordinate set $I$, with independent open probabilities $q_i\\in[0,1]$.", "The events are increasing. Disjoint occurrence always uses finite certificates, as in the disjoint-occurrence article.", "The coordinate set is finite in the first theorem and countable in the extension."],
  "related": ["disjoint-occurrence", "product-model", "harris-inequality", "connectivity"],
  "sourceIds": ["notes", "perclib-low-density-bk"],
  "aliases": ["BK inequality", "van den Berg Kesten", "disjoint witnesses", "countable BK"],
  "prototypeUses": []
}
---

## The finite theorem {#section-finite}

<a id="tag-BNY8" data-assertion="theorem" data-title="Finite-coordinate BK inequality for arbitrary Bernoulli profiles"></a><p>Let $I$ be finite and let $A,B\subseteq\{0,1\}^I$ be increasing. For every profile $q\in[0,1]^I$,</p><div class="math-display">$$\mathbb P_q(A\circ B)\leq\mathbb P_q(A)\mathbb P_q(B).$$</div><p>This is the van den Berg–Kesten inequality, stated in the <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L1223">notes' finite BK statement</a>. It permits inhomogeneous probabilities and both endpoints. The <a href="/tag/E7HI/">deterministic zero-one profile bound</a> is only a special case; its elementary proof does not establish this theorem.</p>

<p>Harris and BK bound different events. Harris gives a lower bound for $\mathbb P(A\cap B)$, whereas BK gives an upper bound for the smaller event $A\circ B$, which requires disjoint witnesses. For a single-edge event $A$, one has $A\circ A=\varnothing$ even though $\mathbb P(A\cap A)=\mathbb P(A)$.</p>

## The finite-coordinate proof {#section-finite-proof}

<p><em>Proof of finite BK.</em> First suppose every coordinate probability is at most $1/2$, and induct on the number of coordinates. The empty product is deterministic, so the assertion holds. For the induction step, single out one coordinate with open probability $p\leq1/2$. Let $A_0,A_1$ be the sections of $A$ with this coordinate forced closed and open, and define $B_0,B_1$ similarly. They are increasing events on the remaining coordinates, with $A_0\subseteq A_1$ and $B_0\subseteq B_1$.</p>
<p>Write $C_{ij}=A_i\circ B_j$. If the distinguished coordinate is closed, disjoint occurrence is exactly $C_{00}$. If it is open, disjoint witnesses use it in at most one of their two certificate sets, so the remaining configuration belongs to $C_{10}\cup C_{01}$. Since $C_{00}$ is contained in both these events, the open section has indicator at most $\mathbf1_{C_{10}}+\mathbf1_{C_{01}}-\mathbf1_{C_{00}}$. Averaging over the distinguished coordinate gives</p>
<div class="math-display">$$\mathbb P(A\circ B)\leq(1-2p)\mathbb P(C_{00})+p\mathbb P(C_{10})+p\mathbb P(C_{01}).$$</div>
<p>The coefficient $1-2p$ is nonnegative, which is the reason for the temporary restriction. Put $a_i=\mathbb P(A_i)$ and $b_i=\mathbb P(B_i)$ under the product law on the remaining coordinates. The induction hypothesis bounds the last display by $(1-2p)a_0b_0+p(a_1b_0+a_0b_1)$. On the other hand,</p>
<div class="math-display">$$\begin{aligned}\mathbb P(A)\mathbb P(B)&=\bigl((1-p)a_0+pa_1\bigr)\bigl((1-p)b_0+pb_1\bigr)\\&=(1-2p)a_0b_0+p(a_1b_0+a_0b_1)+p^2(a_1-a_0)(b_1-b_0).\end{aligned}$$</div>
<p>The last term is nonnegative, completing the induction. The probabilities of the remaining coordinates need not be equal.</p>
<p>Now suppose $q_e&lt;1$ for every coordinate. Replace coordinate $e$ by a finite block of $m_e\geq1$ independent bits, each with probability</p>
<div class="math-display">$$r_e=1-(1-q_e)^{1/m_e},$$</div>
<p>choosing $m_e$ large enough that $r_e\leq1/2$. A coordinate is declared open when at least one bit in its block is open. This map $\pi$ has the original product law as its image, because different blocks are independent and $1-(1-r_e)^{m_e}=q_e$. The lifted events $\widetilde A=\pi^{-1}(A)$ and $\widetilde B=\pi^{-1}(B)$ are increasing.</p>
<p>If $\pi(\omega)\in A\circ B$, choose disjoint open witnesses for $A$ and $B$. For each coordinate in either witness choose one open bit in its block. The resulting bit sets are disjoint because the original coordinate sets were disjoint. They witness $\widetilde A$ and $\widetilde B$: opening those bits opens all original witness coordinates, and increasingness makes the remaining bits irrelevant. Thus $\pi^{-1}(A\circ B)\subseteq\widetilde A\circ\widetilde B$. Applying the low-probability result to the finite bit product gives</p>
<div class="math-display">$$\mathbb P_q(A\circ B)\leq\mathbb P_r(\widetilde A\circ\widetilde B)\leq\mathbb P_r(\widetilde A)\mathbb P_r(\widetilde B)=\mathbb P_q(A)\mathbb P_q(B).$$</div>
<p>Finally, approximate any coordinates with $q_e=1$ by probabilities below one. On a finite product space the probability of each fixed event is a polynomial in the coordinate probabilities, by <a href="/tag/7WIO/">7WIO</a>. The three probabilities in BK therefore converge to their endpoint values. Coordinates of probability zero already cause no difficulty in the block construction. This proves the theorem for every profile in $[0,1]^I$.</p>

<p>The coordinate calculation has a useful algebraic scope. For a finite set $E$ and a real parameter $p$, write</p>
<div class="math-display">$$T_p^E(f)=\sum_{\omega\subseteq E}f(\omega)\prod_{i\in E}\bigl(p\mathbf1_{\{i\in\omega\}}+(1-p)\mathbf1_{\{i\notin\omega\}}\bigr).$$</div>
<p>Splitting this sum into configurations with the distinguished coordinate closed or open gives $T_p(f)=(1-p)T_p(f_0)+pT_p(f_1)$ for every real $p$. A bijection of coordinate sets preserves this sum and carries disjoint finite certificates to disjoint finite certificates, so the induction is independent of the names of its coordinates. The arithmetic remainder $p^2(a_1-a_0)(b_1-b_0)$ is nonnegative for every real $p$ whenever $a_0\leq a_1$ and $b_0\leq b_1$. The empty-coordinate case likewise needs no parameter restriction.</p>
<p>Probability interpretations and monotonicity in the observable require $0\leq p\leq1$, when every weight is nonnegative. The displayed weighted disjoint-occurrence recursion remains valid throughout this probability interval; the narrower condition $p\leq1/2$ is needed when substituting the induction bounds with coefficient $1-2p$. The pinned library module proves this homogeneous low-density case. The inhomogeneous induction, independent-block reduction, endpoint limit and countable extension supplied here are not claimed to be formalized by that module.</p>

## Countably many coordinates {#section-countable}

<a id="tag-JRCI" data-assertion="theorem" data-title="Countable BK for increasing events with finite disjoint witnesses"></a><p>Let $I$ be countable and let $A,B\subseteq\{0,1\}^I$ be measurable increasing events. Their finite-certificate disjoint occurrence $A\circ B$ is measurable, and</p><div class="math-display">$$\mathbb P_q(A\circ B)\leq\mathbb P_q(A)\mathbb P_q(B).$$</div><p><em>Proof.</em> Choose increasing finite sets $I_n$ exhausting $I$. On configurations $\eta\subseteq I_n$, define</p><div class="math-display">$$A_n=\{\eta:\text{there is }F\subseteq\eta\text{ with }F\in A\},\qquad B_n=\{\eta:\text{there is }H\subseteq\eta\text{ with }H\in B\},$$</div><p>where $F,H$ are regarded as configurations on all of $I$, with other coordinates closed. These are increasing finite-coordinate events. If $\omega\cap I_n\in A_n$, then some $F\subseteq\omega$ belongs to $A$, and increasingness gives $\omega\in A$. Thus $\mathbb P_q(\omega\cap I_n\in A_n)\leq\mathbb P_q(A)$, and similarly for $B$.</p><p>Let $D_n=\{\omega:\omega\cap I_n\in A_n\circ B_n\}$. By the <a href="/tag/HRBD/">open-witness characterization</a>, $D_n$ is exactly the event that disjoint finite witnesses for $A$ and $B$ can be chosen inside $I_n$. Indeed, witnesses for $A_n$ and $B_n$ contain, by their definitions, disjoint sub-witnesses belonging to $A$ and $B$; the converse uses those sub-witnesses directly. Consequently $D_n$ increases to $A\circ B$. Each $D_n$ is a cylinder event, so this also proves measurability. Finite BK bounds every $\mathbb P_q(D_n)$ by $\mathbb P_q(A)\mathbb P_q(B)$. Continuity from below finishes the proof.</p>

<p>This argument does not require every occurrence of $A$ or $B$ to have a finite witness. It only exhausts the witnesses already required by $A\circ B$. In particular, it does not claim that the events $A_n$ exhaust $A$: for the event that infinitely many coordinates are open, no finite open configuration belongs to $A$.</p>

## Repeated disjoint occurrence {#section-repeated}

<a id="tag-AUUG" data-assertion="corollary" data-title="Product bound for finitely many disjoint increasing events"></a><p>For measurable increasing events $A_1,\ldots,A_m$ on a countable coordinate set, with $m\geq2$,</p><div class="math-display">$$\mathbb P_q(A_1\circ\cdots\circ A_m)\leq\prod_{j=1}^m\mathbb P_q(A_j).$$</div><p>Here the event requires $m$ pairwise disjoint finite open witnesses, one for each $A_j$.</p><p><em>Proof.</em> The <a href="/tag/HP3X/">associativity and open-witness identity</a> identify successive disjoint occurrence with the stated witness condition. The two-event result shows inductively that each intermediate event is measurable; it is increasing by its open-witness description. Applying the two-event inequality at each step proves the product bound.</p>

<p>For connection events on a countable graph, finite open paths supply the witnesses. Paths may share vertices; BK requires their edge sets to be disjoint. A tree joining several specified vertices supplies the relevant disjoint paths only after its branch points have been chosen, which is why tree-graph bounds sum over branch locations.</p>

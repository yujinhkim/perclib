---
{
  "id": "cutoff-scaling",
  "title": "Cutoff scaling relations",
  "subtitle": "What uniform tail and two-point estimates imply",
  "kind": "method",
  "category": "Critical theory",
  "summary": "Explicit cutoff hypotheses yield moment scales and familiar exponent identities. The estimates explain the scaling argument without assuming that its hypotheses hold in a given percolation model.",
  "context": ["The notation $f\\asymp g$ means two-sided bounds by positive constants independent of the parameter tending to its limit.", "The cutoff estimates below are hypotheses, not asserted properties of every percolation model.", "Cluster-volume variables are positive integer-valued; expectations may initially be extended nonnegative quantities."],
  "related": ["criticality", "susceptibility", "binary-tree-percolation", "triangle-condition", "cutoff-families"],
  "sourceIds": ["notes"],
  "aliases": ["scaling relations", "gap exponent", "gap scale", "moment cutoff", "correlation length", "Fisher relation"],
  "prototypeUses": []
}
---

## A volume cutoff {#section-volume}

<a id="tag-QT3F" data-assertion="theorem" data-title="Uniform power-law cutoff bounds determine moment scales"></a><p>Fix $0&lt;a&lt;1$. Let $(T_z)_{z\geq2}$ be positive integer-valued random variables. Suppose constants $c,C,b&gt;0$, independent of $z$, satisfy</p><div class="math-display">$$\mathbb P(T_z\geq n)\leq Cn^{-a}e^{-bn/z}\quad(n\geq1),\qquad \mathbb P(T_z\geq n)\geq cn^{-a}\quad(1\leq n\leq z).$$</div><p>For every fixed real $k&gt;a$,</p><div class="math-display">$$\mathbb E T_z^k\asymp z^{k-a}.$$</div><p>In particular, $\mathbb E T_z\asymp z^{1-a}$ and $\mathbb E T_z^2/\mathbb E T_z\asymp z$. The constants in the moment estimate may depend on $k$.</p><p><em>Proof.</em> Summation of the increments of $n^k$ gives the exact identity</p><div class="math-display">$$\mathbb E T_z^k=\sum_{n=1}^{\infty}\bigl(n^k-(n-1)^k\bigr)\mathbb P(T_z\geq n).$$</div><p>For fixed $k&gt;0$, the increment is comparable to $n^{k-1}$. The lower bound therefore dominates a constant times $\sum_{n\leq z}n^{k-a-1}$, which is comparable to $z^{k-a}$ because $k&gt;a$. For the upper bound, the same comparison gives $\sum_{n\geq1}n^{k-a-1}e^{-bn/z}$. Split at $z$ and then into blocks $2^jz&lt;n\leq2^{j+1}z$. The first block is $O(z^{k-a})$; the later blocks are bounded by a constant times $z^{k-a}2^{(j+1)(k-a)}e^{-b2^j}$, whose coefficients are summable. This also proves finiteness of the moments in question. Taking $k=1,2$ gives the ratio statement.</p>

<p>The exact tail sum starts at $n=1$. A term at $n=0$ would add one in the first-moment identity; this is the indexing correction recorded in the source audit. The cutoff hypothesis is stronger than a statement about logarithmic exponents alone.</p>

## Consequences for volume exponents {#section-exponents}

<a id="tag-ADN0" data-assertion="corollary" data-title="Volume scaling identities under cutoff and matching hypotheses"></a><p>Suppose the preceding bounds hold uniformly along a subcritical family, with $a=1/\delta$, $\delta&gt;1$, cutoff $z(\varepsilon)\asymp\varepsilon^{-\Delta}$ and $\Delta&gt;0$, where $\varepsilon\downarrow0$ measures distance from criticality. Then</p><div class="math-display">$$\chi(\varepsilon)\asymp\varepsilon^{-\gamma},\qquad \gamma=\frac{\delta-1}{\delta}\Delta,$$</div><p>and for each fixed $k&gt;1/\delta$,</p><div class="math-display">$$\mathbb E T_{z(\varepsilon)}^k\asymp\varepsilon^{-\gamma-(k-1)\Delta}.$$</div><p>If, in addition, a supercritical survival probability satisfies the separate matching assumption $\theta(\varepsilon)\asymp z(\varepsilon)^{-1/\delta}$, then its exponent is $\beta=\Delta/\delta$, and $\beta+\gamma=\Delta$.</p><p><em>Proof.</em> Substitute the cutoff scale into the moment estimate. The identity $k-1/\delta=(1-1/\delta)+(k-1)$ gives the displayed exponent. The additional matching assumption gives $\beta$ directly; adding the two exponents gives $\Delta$.</p><p>The subcritical tail bounds do not imply the supercritical matching assumption. It expresses additional information about how finite clusters and the infinite cluster fit together across the transition.</p>

## A spatial cutoff {#section-spatial}

<a id="tag-CAV9" data-assertion="theorem" data-title="Radial two-point cutoff bounds determine susceptibility scaling"></a><p>On $\mathbb Z^d$, let $d\geq1$, $2-d\leq\eta&lt;2$, and $\xi\geq2$. Suppose $\tau_\xi(0)=1$ and, writing $r=\|x\|_\infty$, there are constants $c,C,b&gt;0$ independent of $\xi$ such that</p><div class="math-display">$$\tau_\xi(x)\leq Cr^{-d+2-\eta}e^{-br/\xi}\quad(x\neq0),\qquad \tau_\xi(x)\geq cr^{-d+2-\eta}\quad(1\leq r\leq\xi).$$</div><p>Then $\sum_x\tau_\xi(x)\asymp\xi^{2-\eta}$. If $\xi(\varepsilon)\asymp\varepsilon^{-\nu}$, this gives the susceptibility exponent $\gamma=(2-\eta)\nu$.</p><p><em>Proof.</em> The shell $\{x:\|x\|_\infty=r\}$ has $(2r+1)^d-(2r-1)^d\asymp r^{d-1}$ vertices. Summing the lower bound through $r\leq\xi$ gives $\sum_{r\leq\xi}r^{1-\eta}\asymp\xi^{2-\eta}$. Summing the upper bound gives the corresponding exponentially cut off series, bounded by the same dyadic-block argument as above. The root contributes one, which is absorbed because $2-\eta&gt;0$.</p>

<p>For a two-point function bounded by one, the restriction $\eta\geq2-d$ makes the lower-bound hypothesis compatible with arbitrarily large cutoffs. An exponential spatial cutoff is a short-range assumption; it should not be transferred without proof to a long-range model whose two-point function has a polynomial tail. At $\eta=2$ the shell sum is logarithmic, so the stated power-law conclusion does not extend to that endpoint.</p>

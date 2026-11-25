---
{
  "id": "exponential-moments",
  "title": "From tree-graph moments to exponential tails",
  "subtitle": "Summing the moment series without losing the endpoint",
  "kind": "method",
  "category": "Methods",
  "summary": "Double-factorial moment bounds control both weighted and ordinary exponential moments. Explicit Markov bounds retain their prefactors and yield a pure exponential estimate only in a stated large-threshold range.",
  "context": ["A nonnegative random variable $X$ with finite positive mean $\\chi$.", "The full moment hypothesis is $\\mathbb E X^m\\leq(2m-3)!!\\,\\chi^{2m-1}$ for every integer $m\\geq1$, with $(-1)!!=1$.", "For percolation, deriving these moment inequalities is a separate tree-graph argument."],
  "related": ["susceptibility", "sharpness", "disjoint-occurrence", "universal-tightness"],
  "sourceIds": ["notes"],
  "aliases": ["exponential moment", "moment generating function", "tree-graph moments", "double factorial", "subcritical volume tail"],
  "prototypeUses": []
}
---

## Summing the moment bounds {#section-series}

<a id="tag-0BQB" data-assertion="theorem" data-title="Exponential moments from double-factorial moment bounds"></a><p>Suppose $X\geq0$, $\chi=\mathbb E X\in(0,\infty)$, and</p><div class="math-display">$$\mathbb E X^m\leq(2m-3)!!\,\chi^{2m-1}\qquad(m=1,2,\ldots),$$</div><p>where $(-1)!!=1$. For $0\leq r&lt;(2\chi^2)^{-1}$,</p><div class="math-display">$$\mathbb E[Xe^{rX}]\leq\frac\chi{\sqrt{1-2r\chi^2}}.$$</div><p>The ordinary exponential moment also satisfies</p><div class="math-display">$$\mathbb E e^{rX}\leq1+\frac{1-\sqrt{1-2r\chi^2}}\chi\qquad\left(0\leq r\leq\frac1{2\chi^2}\right).$$</div><p>In particular, the second bound includes its upper endpoint, where it gives $\mathbb E e^{X/(2\chi^2)}\leq1+\chi^{-1}$.</p><p><em>Proof.</em> All terms in the exponential series are nonnegative, so Tonelli and the moment hypothesis give</p><div class="math-display">$$\mathbb E[Xe^{rX}]=\sum_{j\geq0}\frac{r^j}{j!}\mathbb E X^{j+1}\leq\chi\sum_{j\geq0}\frac{(2j-1)!!}{j!}(r\chi^2)^j=\frac\chi{\sqrt{1-2r\chi^2}}.$$</div><p>The last equality is the binomial series, using $(2j-1)!!/j!=2^{-j}\binom{2j}{j}$. Integrate the bound from zero to $r$. Since $e^{rX}-1=\int_0^rXe^{sX}\,ds$, Tonelli gives</p><div class="math-display">$$\mathbb E e^{rX}-1\leq\int_0^r\frac\chi{\sqrt{1-2s\chi^2}}\,ds=\frac{1-\sqrt{1-2r\chi^2}}\chi.$$</div><p>This proves the ordinary-moment bound below the endpoint. Letting $r\uparrow(2\chi^2)^{-1}$ and using monotone convergence proves the endpoint assertion. The square-root singularity of the weighted bound is integrable; it does not obstruct this finite ordinary exponential moment.</p><p>Finite mean alone would not justify any of these conclusions. The assumption controls all positive integer moments with a particular growth rate. It also implies that each of those moments is finite, so the power-series calculation does not assume the desired exponential integrability in advance.</p>

## Tail estimates with their constants {#section-tails}

<a id="tag-SNB3" data-assertion="corollary" data-title="Explicit exponential tails and the large-threshold prefactor removal"></a><p>Under the preceding hypotheses, for every real $n&gt;0$,</p><div class="math-display">$$\mathbb P(X\geq n)\leq\min\left\{1,\ \frac{\sqrt2\chi}{n}e^{-n/(4\chi^2)},\ (1+\chi^{-1})e^{-n/(2\chi^2)}\right\}.$$</div><p>In particular, for</p><div class="math-display">$$n\geq4\chi^2\log(1+\chi^{-1}),$$</div><p>one has $\mathbb P(X\geq n)\leq e^{-n/(4\chi^2)}$.</p><p><em>Proof.</em> On $\{X\geq n\}$, $Xe^{rX}\geq ne^{rn}$. Taking $r=(4\chi^2)^{-1}$ in the weighted bound gives the second entry in the minimum. Markov's inequality applied to the ordinary exponential moment at $r=(2\chi^2)^{-1}$ gives the third. The stated lower bound on $n$ makes $1+\chi^{-1}\leq e^{n/(4\chi^2)}$, allowing the prefactor in that third entry to be absorbed. Probabilities are also at most one.</p><p>For a bond cluster, $X=|K_o|\geq1$ almost surely. Thus an estimate $\mathbb P(X\geq n)\leq e^{-cn}$ with $c&gt;0$ cannot hold at $n=1$. The explicit prefactors above, or the stated eventual range, avoid this endpoint error. No change to the fact that the cluster contains its root is made to obtain the tail estimate.</p>

## A fourth-to-second moment comparison {#section-log-ratio}

<a id="tag-IXEZ" data-assertion="proposition" data-title="A logarithmic fourth-moment comparison from the weighted exponential bound"></a>
<p>Let $X\geq0$, $\chi=\mathbb E X\geq1$, and assume $\mathbb E[Xe^{X/(4\chi^2)}]\leq\sqrt2\chi$. Then</p>
<div class="math-display">$$\mathbb E X^4\leq1152\chi^4\log^2(2\chi)\,\mathbb E X^2.$$</div>
<p>In particular, this holds for a transitive independent bond model with finite susceptibility, by <a href="/tag/0BQB/">0BQB</a>.</p>
<p><em>Proof.</em> Set $T=24\chi^2\log(2\chi)$ and $s=(4\chi^2)^{-1}$. On $X\leq T$, use $X^4\leq T^2X^2$. Since $T\geq12\chi^2$, the function $x^3e^{-sx}$ is decreasing on $[T,\infty)$. Hence</p>
<div class="math-display">$$\mathbb E[X^4\mathbf1_{\{X&gt;T\}}]\leq T^3e^{-sT}\mathbb E[Xe^{sX}]\leq\sqrt2\chi T^3(2\chi)^{-6}.$$</div>
<p>Jensen gives $\mathbb E X^2\geq\chi^2$. The last upper bound divided by $T^2\mathbb E X^2$ is therefore at most</p>
<div class="math-display">$$\frac{\sqrt2 T}{\chi}(2\chi)^{-6}=\frac{3\sqrt2}{8}\frac{\log(2\chi)}{\chi^5}\leq\frac{3\sqrt2}{8}&lt;1,$$</div>
<p>where $\log(2\chi)\leq\chi$ for $\chi\geq1$. Adding the two parts gives $\mathbb E X^4\leq2T^2\mathbb E X^2$, as claimed. The exponential hypothesis ensures that all moments used here are finite.</p>
<p>The logarithmic loss is deliberate. This does not prove the stronger comparison without that loss in the notes' higher-moment discussion. It is nevertheless enough to make the second-moment differential error integrable whenever its power of radius is strictly decaying.</p>

## Uniform susceptibility in an inhomogeneous model {#section-uniform}

<a id="tag-XLWI" data-assertion="theorem" data-title="Uniform susceptibility gives exponential bounds with the root mean retained"></a>
<p>Consider independent bond percolation on a nonempty countable vertex set. Write $\chi_x=\mathbb E|K_x|$, and suppose $M=\sup_x\chi_x&lt;\infty$. For every root $o$ and $0\leq s&lt;(2M^2)^{-1}$,</p>
<div class="math-display">$$\mathbb E\bigl[|K_o|e^{s|K_o|}\bigr]\leq\frac{\chi_o}{\sqrt{1-2sM^2}}.$$</div>
<p>For $0\leq s\leq(2M^2)^{-1}$, including the upper endpoint,</p>
<div class="math-display">$$\mathbb E e^{s|K_o|}\leq1+\frac{\chi_o}{M^2}\bigl(1-\sqrt{1-2sM^2}\bigr).$$</div>
<p>Consequently, for every real $n&gt;0$,</p>
<div class="math-display">$$\mathbb P(|K_o|\geq n)\leq\min\left\{1,\ \frac{\sqrt2\chi_o}{n}e^{-n/(4M^2)},\ \left(1+\frac{\chi_o}{M^2}\right)e^{-n/(2M^2)}\right\}.$$</div>
<p>In particular, $\mathbb P(|K_o|\geq n)\leq e^{-n/(4M^2)}$ whenever $n\geq4M^2\log(1+\chi_o/M^2)$.</p>
<p><em>Proof.</em> The <a href="/tag/Y84V/">uniform-susceptibility tree-graph bound</a> gives $\mathbb E|K_o|^{j+1}\leq(2j-1)!!\,\chi_oM^{2j}$ for $j\geq0$. Sum the nonnegative exponential series:</p>
<div class="math-display">$$\mathbb E\bigl[|K_o|e^{s|K_o|}\bigr]\leq\chi_o\sum_{j\geq0}\frac{(2j-1)!!}{j!}(sM^2)^j=\frac{\chi_o}{\sqrt{1-2sM^2}}.$$</div>
<p>Integration from zero to $s$ gives the ordinary exponential bound below the endpoint. Monotone convergence extends it to $s=(2M^2)^{-1}$. Apply Markov's inequality to the weighted exponential at $s=(4M^2)^{-1}$ and to the ordinary exponential at its endpoint. The final threshold absorbs the prefactor in the latter bound.</p>
<p>No transitivity is required. The scale uses the susceptibility supremum $M$, while the prefactors retain the mean at the chosen root. When all susceptibilities equal $\chi$, these formulas recover the preceding bounds. The <a href="/tag/HRS7/">root-mean counterexample</a> explains why a finite value of $\chi_o$ alone cannot replace the uniform hypothesis.</p>

## From cluster volume to spatial radius {#section-finite-range}

<a id="tag-YVJT" data-assertion="corollary" data-title="Uniformly finite susceptibility gives spatial exponential decay for finite-range bonds"></a>
<p>Consider independent bonds on $\mathbb Z^d$. Suppose bonds with $\|x-y\|_\infty&gt;R$ have probability zero, where $R&gt;0$, and let $M=\sup_x\mathbb E|K_x|&lt;\infty$, $\chi_o=\mathbb E|K_o|$. Then, for $r\geq0$,</p>
<div class="math-display">$$\mathbb P\bigl(o\leftrightarrow\mathbb Z^d\setminus(o+[-r,r]^d)\bigr)\leq\sqrt2\chi_o\exp\!\left(-\frac{r}{4RM^2}\right).$$</div>
<p><em>Proof.</em> A simple open path from $o$ to a vertex outside the box has more than $r/R$ edges, since each edge changes the sup norm by at most $R$. Its vertices are distinct and belong to $K_o$. In particular, the exit event implies $|K_o|\geq n$ for $n=\lfloor r/R\rfloor+1$. The <a href="/tag/XLWI/">uniform-susceptibility volume bound</a> gives</p>
<div class="math-display">$$\mathbb P(|K_o|\geq n)\leq\frac{\sqrt2\chi_o}{n}e^{-n/(4M^2)}\leq\sqrt2\chi_o e^{-r/(4RM^2)},$$</div>
<p>as required.</p>
<p>For homogeneous nearest-neighbour percolation, take $R=1$ and $M=\chi_o$. The <a href="/articles/integrated-susceptibility/#section-finite-set">finite-set sharpness proof</a> makes this mean finite throughout the subcritical phase, proving the spatial conclusion of <a href="/tag/6THJ/">lattice sharpness</a> with explicit, non-optimal constants.</p>
<p>The range assumption cannot be dropped. For a power-law intensity kernel and $\beta&gt;0$, a single edge gives $\tau_\beta(0,x)\geq1-e^{-\beta J(x)}$. If $J(x)\asymp\|x\|^{-d-\alpha}$, this lower bound is polynomial at large distance and rules out a uniform exponential spatial bound, even at parameters with exponential cluster-volume tails.</p>

## Where the probabilistic input enters {#section-input}

<p>The <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L1349">end of the tree-graph section in the notes</a> uses the weighted moment series to deduce subcritical exponential decay. The analytic implication here begins only after the double-factorial moment inequalities have been established. In a percolation application, their proof must supply the required independence, geometry and summation arguments. Likewise, identifying the region of finite susceptibility with the full subcritical phase is a separate sharpness input.</p><p>The unqualified $n\geq1$ exponential bound in the source sharpness statement is the endpoint issue recorded as N-ERR-02 in the source audit. The estimates here provide precise forms that follow from the displayed moment hypothesis. They do not replace the separate <a href="/articles/sharpness/">model-specific sharpness theorem</a>, and the scale $\chi^2$ in these bounds need not be an optimal decay scale for every model.</p>

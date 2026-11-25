---
{
  "id": "size-biased-laws",
  "title": "Size-biased laws, cutoff limits and critical trees",
  "subtitle": "Moment ratios, cutoff distributions and conditioning on distant survival",
  "kind": "method",
  "category": "Methods",
  "summary": "Size bias converts cluster moment asymptotics into volume and random-measure limits. Local moments and spatial tightness identify the canonical measure; ghost comparison controls removal of the cutoff.",
  "context": [
    "Size bias by $X$ requires $X\\geq0$ and $0<\\mathbb E X<\\infty$.",
    "For the distant-survival limits and quadratic tree asymptotics, a Galton–Watson process starts from one individual, with offspring mean one and variance $\\sigma^2\\in(0,\\infty)$.",
    "$Z_r$ is the population of generation $r$; $\\mathcal F_r$ records the tree through generation $r$, before its individuals reproduce."
  ],
  "related": [
    "branching-processes",
    "binary-tree-percolation",
    "susceptibility",
    "universal-tightness",
    "ghost-fields",
    "regular-variation",
    "spatial-cutoff-moments"
  ],
  "sourceIds": [
    "notes",
    "hutchcroft-lrp-1"
  ],
  "aliases": [
    "size bias",
    "size biased",
    "incipient infinite cluster",
    "IIC",
    "gap scale",
    "moment ratio"
  ],
  "prototypeUses": []
}
---

## Biasing by mass {#section-size-bias}

<a id="tag-6L9Z" data-assertion="definition" data-title="Size-biased probability law"></a><p>For a nonnegative random variable $X$ with $0&lt;\mathbb E X&lt;\infty$, its size-biased law on the underlying sample space is</p><div class="math-display">$$\widehat{\mathbb P}(A)=\frac{\mathbb E[X\mathbf1_A]}{\mathbb E X}.$$</div><p>Thus, for nonnegative $F$, $\widehat{\mathbb E}F=\mathbb E[XF]/\mathbb E X$. In particular,</p><div class="math-display">$$\widehat{\mathbb E}X=\frac{\mathbb E X^2}{\mathbb E X},$$</div><p>allowing an infinite second moment. For cluster volume $T$ with finite susceptibility, this ratio is the expected volume under volume bias. It is one possible gap scale. If $\mathbb E T=\infty$, the displayed formula does not define a probability law; an expression of the form $\infty/\infty$ supplies no normalization.</p>

## A branching-process cutoff law {#section-branching-cutoff}

<a id="tag-0OEW" data-assertion="theorem" data-title="Near-critical finite-progeny size bias converges to a squared normal"></a>
<p>Let $\xi_j$ converge in distribution to a nondegenerate critical offspring variable $\xi$, with variance $\sigma^2\in(0,\infty)$, and suppose $(\xi_j^2)$ is uniformly integrable. Write $\varepsilon_j=\mathbb E\xi_j-1$, assume $\varepsilon_j\ne0$, and put $\delta_j=|\varepsilon_j|$. Let $T_j$ be total progeny from one ancestor and</p>
<div class="math-display">$$s_j=\mathbb E[T_j;\,T_j&lt;\infty].$$</div>
<p>For all sufficiently large $j$, $0&lt;s_j&lt;\infty$ and $\delta_js_j\to1$. Define the probability law $Q_j$ on $[0,\infty)$ by</p>
<div class="math-display">$$\int f(y)\,dQ_j(y)=
\frac{\mathbb E[T_j f(\delta_j^2T_j);\,T_j&lt;\infty]}{s_j}
$$</div>
<p>for bounded nonnegative $f$. Then $Q_j$ converges weakly to the law of $\sigma^2Z^2$, where $Z$ is a standard normal variable. The signs of $\varepsilon_j$ may vary. Above criticality this biases only finite progeny; the unconditional mean of $T_j$ is infinite and cannot normalize a probability law.</p>
<p><em>Proof.</em> Let $\phi_j$ be the offspring generating function and $q_j=\mathbb P(T_j&lt;\infty)$. The critical limit and the fixed-point argument give $q_j\to1$. Below criticality $q_j=1$. Above criticality <a href="/tag/N9P5/">N9P5</a> gives $1-q_j\sim2\varepsilon_j/\sigma^2$. Uniform integrability also gives the derivative expansion</p>
<div class="math-display">$$\phi_j'(1-u)=1+\varepsilon_j-\sigma^2u+o(u)
\qquad(j\to\infty,\ u\downarrow0),$$</div>
<p>with zero error at $u=0$. It follows on both sides that</p>
<div class="math-display">$$1-\phi_j'(q_j)\sim\delta_j.$$</div>
<p>For $h&gt;0$, differentiate the progeny generating equation, writing $M_j(h)$ as in <a href="/tag/DGVA/">DGVA</a>. Differentiation under the expectation is valid since $t e^{-ht}$ is bounded. This gives</p>
<div class="math-display">$$\mathbb E[T_j e^{-hT_j};\,T_j&lt;\infty]
=\frac{1-M_j(h)}{1-e^{-h}\phi_j'(1-M_j(h))}.$$</div>
<p>For sufficiently large $j$, $q_j&gt;0$ and $1-\phi_j'(q_j)&gt;0$. Letting $h\downarrow0$ and applying monotone convergence therefore proves</p>
<div class="math-display">$$s_j=\frac{q_j}{1-\phi_j'(q_j)}\sim\delta_j^{-1}.$$</div>
<p>Now fix $\lambda&gt;0$ and take $h=\lambda\delta_j^2$. The joint crossover gives</p>
<div class="math-display">$$\frac{M_j(\lambda\delta_j^2)}{\delta_j}
=\frac{\operatorname{sgn}(\varepsilon_j)+\sqrt{1+2\sigma^2\lambda}}{\sigma^2}+o(1).$$</div>
<p>In particular $M_j(\lambda\delta_j^2)$ is of order $\delta_j$, even if the signs alternate. The derivative expansion and $h=O(\delta_j^2)$ yield</p>
<div class="math-display">$$1-e^{-h}\phi_j'(1-M_j(h))
=\delta_j\sqrt{1+2\sigma^2\lambda}+o(\delta_j).$$</div>
<p>Dividing the differentiated identity by $s_j$ shows that the Laplace transform of $Q_j$ tends to $(1+2\sigma^2\lambda)^{-1/2}$. This is the transform of $\sigma^2Z^2$, by a Gaussian integral, and it is continuous at $\lambda=0$ with value one. The continuity theorem for Laplace transforms proves weak convergence.</p>
<p>Only a uniformly integrable offspring second moment is used. No higher total-progeny moments are assumed, and weak convergence alone is not a claim that all such moments converge. The result supplies a branching-process instance of the squared-normal cutoff law; it is not a percolation or spatial scaling-limit theorem.</p>

## Finite tails across the branching cutoff {#section-branching-tails}

<a id="tag-KOY8" data-assertion="corollary" data-title="Near-critical finite-progeny tail and ghost limits at a fixed cutoff scale"></a>
<p>Under the hypotheses of <a href="/tag/0OEW/">0OEW</a>, for each fixed $x&gt;0$ and $\lambda&gt;0$,</p>
<div class="math-display">$$\frac{\mathbb P(x\delta_j^{-2}\leq T_j&lt;\infty)}{\delta_j}
\longrightarrow
\frac1{\sqrt{2\pi\sigma^2}}\int_x^\infty y^{-3/2}e^{-y/(2\sigma^2)}\,dy,$$</div>
<div class="math-display">$$\frac{\mathbb E[1-e^{-\lambda\delta_j^2T_j};\,T_j&lt;\infty]}{\delta_j}
\longrightarrow\frac{\sqrt{1+2\sigma^2\lambda}-1}{\sigma^2}.$$</div>
<p>Both limits hold along arbitrary changes of sign of $\varepsilon_j$. For unrestricted tails on the supercritical subsequence, the atom at infinity contributes an additional limit $2/\sigma^2$ after division by $\delta_j$; on the subcritical subsequence it contributes zero.</p>
<p><em>Proof.</em> Apply <a href="/tag/7W00/">the size-bias transfer identities</a> to the finite-valued random variable equal to $T_j$ on $\{T_j&lt;\infty\}$ and zero otherwise, with scale $\delta_j^{-2}$ and mean $s_j$. Since $\delta_js_j\to1$, its tail and finite ghost transform, divided by $\delta_j$, have respective limits</p>
<div class="math-display">$$\int_{[x,\infty)}y^{-1}\,dQ(y),\qquad
\int_{[0,\infty)}\frac{1-e^{-\lambda y}}y\,dQ(y),\qquad Q=\operatorname{Law}(\sigma^2Z^2).$$</div>
<p>The density of $Q$ gives the first displayed formula. For the second, write $(1-e^{-\lambda y})/y=\int_0^\lambda e^{-ty}\,dt$ and integrate $(1+2\sigma^2t)^{-1/2}$ over $0\leq t\leq\lambda$. The survival asymptotic N9P5 gives the contribution from infinite progeny.</p>
<p>These statements concern tails and transforms at fixed positive cutoff scales. They remain valid with periodic progeny support, including zero-or-two offspring; they do not imply a point-probability equivalent at every integer or a limit uniform as $x\downarrow0$. For binary-tree percolation, $\sigma^2=1/2$ and $\delta=|2p-1|$, in agreement with its <a href="/tag/V5OZ/">explicit finite-cluster cutoff</a>.</p>

## A squared-normal cutoff limit {#section-cutoff-limit}

<a id="tag-0N85" data-assertion="theorem" data-title="Squared-normal size-biased limit from cutoff moment asymptotics"></a>
<p>Let $X_r\geq0$ have finite moments of every positive integer order, with $m_r=\mathbb E X_r&gt;0$, and set $a_r=\mathbb E X_r^2/m_r$. Let $Q_r$ be the law of $X_r/a_r$ under size bias by $X_r$. Suppose, for every integer $p\geq1$,</p>
<div class="math-display">$$\frac{\mathbb E X_r^{p+1}}{m_r a_r^p}\longrightarrow(2p-1)!!\qquad(r\to\infty).$$</div>
<p>Then $Q_r$ converges weakly to the law of $N^2$, where $N$ is a standard normal variable.</p>
<p><em>Proof.</em> Under $Q_r$ the $p$th moment is exactly the ratio in the hypothesis. The first moment is one, so Markov's inequality makes the family tight. Along any weakly convergent subsequence, bounded $(p+1)$st moments make the $p$th powers uniformly integrable: their expectations on $X_r/a_r&gt;A$ are bounded by $A^{-1}$ times the $(p+1)$st moment. Truncation therefore shows that any subsequential limit $Y$ has moments $\mathbb E Y^p=(2p-1)!!$.</p>
<p>These moments determine a unique law. For $0\leq t&lt;1/2$, Tonelli and the binomial series give</p>
<div class="math-display">$$\mathbb E e^{tY}=\sum_{p=0}^\infty\frac{t^p(2p-1)!!}{p!}=(1-2t)^{-1/2},$$</div>
<p>where $(-1)!!=1$. This is the moment generating function of $N^2$, obtained by a Gaussian integral. A moment generating function finite in a neighbourhood of zero determines its law. Hence every subsequential limit is $N^2$, and tightness gives convergence of the whole family.</p>
<p>This supplies the probability argument in the notes' size-biased cutoff corollary, lines 5180–5205 (S033). The model-specific cutoff moment asymptotics are the input; weak convergence is not deduced from only the first two moments.</p>

## Reading cutoff tails and ghost transforms {#section-cutoff-transforms}

<a id="tag-7W00" data-assertion="proposition" data-title="Tail and ghost-transform limits under convergent size-biased laws"></a>
<p>More generally, let $X_r\geq0$ have $0&lt;m_r=\mathbb E X_r&lt;\infty$, choose any scales $a_r&gt;0$, and suppose the laws $Q_r$ of $X_r/a_r$ under size bias converge weakly to a probability law $Q$ on $[0,\infty)$. For every $t&gt;0$ with $Q(\{t\})=0$,</p>
<div class="math-display">$$\frac{a_r}{m_r}\mathbb P(X_r\geq t a_r)\longrightarrow\int_{[t,\infty)}\frac1y\,dQ(y).$$</div>
<p>If $h_r&gt;0$ and $h_ra_r\to\lambda\in(0,\infty)$, then</p>
<div class="math-display">$$\frac{a_r}{m_r}\mathbb E[1-e^{-h_rX_r}]\longrightarrow\int_{[0,\infty)}\frac{1-e^{-\lambda y}}y\,dQ(y),$$</div>
<p>where the integrand at $y=0$ is defined to be $\lambda$. No assumption excluding an atom of $Q$ at zero is needed for this fixed-$\lambda$ limit.</p>
<p><em>Proof.</em> Size bias gives the exact identities with $Q_r$ on the right and with $\lambda$ replaced by $h_ra_r$ in the second. The first test function $y^{-1}\mathbf1_{[t,\infty)}(y)$, set to zero at zero, is bounded and continuous except at $t$. The condition $Q(\{t\})=0$ therefore permits weak convergence to be applied to it.</p>
<p>For the second identity write $f_\lambda(y)=(1-e^{-\lambda y})/y=\int_0^\lambda e^{-sy}\,ds$, including at zero. This is bounded and continuous, and</p>
<div class="math-display">$$\sup_{y\geq0}|f_\lambda(y)-f_\mu(y)|\leq|\lambda-\mu|.$$</div>
<p>Weak convergence applies to $f_\lambda$, while this uniform estimate permits the parameter $h_ra_r$ to vary. That proves the second limit.</p>
<p>For $Q$ equal to the law of $N^2$, these limits are respectively</p>
<div class="math-display">$$\frac1{\sqrt{2\pi}}\int_t^\infty y^{-3/2}e^{-y/2}\,dy,\qquad \sqrt{1+2\lambda}-1.$$</div>
<p>The first follows from the density of $N^2$. For the second, Tonelli gives $\mathbb E f_\lambda(N^2)=\int_0^\lambda(1+2s)^{-1/2}\,ds$.</p>
<p>These are statements at a fixed positive cutoff scale. They do not justify sending $t$ to zero or $\lambda$ to infinity together with $r$. Nor do they identify the tail of the full, untruncated model. The notes' subsequent proposition (S034, lines 5210–5314) also uses a cutoff-to-full comparison and control of the omitted-edge kernel; the next theorem makes those inputs explicit and justifies the further order of limits.</p>

## Comparing a cutoff with the full graph {#section-cutoff-comparison}

<a id="tag-FJWB" data-assertion="proposition" data-title="Ghost comparison from an omitted-edge row bound"></a>
<p>Consider independent bonds on a countable vertex set $V$, with probabilities $q(u,v)=q(v,u)\in[0,1]$ for $u\neq v$. Fix a deterministic set $E_0$ of retained bonds, and form the cutoff graph by closing every bond outside $E_0$. Suppose its cluster at $o$ has finite size $X$ almost surely, and</p>
<div class="math-display">$$\delta=\sup_{u\in V}\sum_{\substack{v\neq u\\\{u,v\}\notin E_0}}q(u,v)&lt;\infty.$$</div>
<p>Mark vertices independently green with probability $1-e^{-h}$, where $h&gt;0$. Let $M_o(h)$ be the full-graph ghost-connection probability, $M_0(h)=\mathbb E[1-e^{-hX}]$ its cutoff counterpart, and $M^*(h)=\sup_v M_v(h)$. Then</p>
<div class="math-display">$$M_0(h)\leq M_o(h)\leq M_0(h)+\delta\,\mathbb E[Xe^{-hX}]M^*(h).$$</div>
<p>In particular, if the full law is transitive, $M^*(h)=M_o(h)$ and the error is multiplicative.</p>
<p><em>Proof.</em> Couple the two graphs by using the same retained bonds and the same green marks. The lower bound follows immediately. For the upper bound, condition on the cutoff cluster being a finite set $S$. Its retained boundary edges are closed. The event determining $S$ uses no omitted edges and no edges with both endpoints outside $S$, so those coordinates retain their product law. Marks also remain independent; the probability that $S$ contains no green vertex is $e^{-h|S|}$.</p>
<p>If the full cluster reaches a green vertex while $S$ contains none, take a finite open path from $o$ to a green vertex and consider its last exit from $S$. That exit is an omitted edge $\{u,v\}$ with $u\in S$ and $v\notin S$, followed by a path to a green vertex entirely outside $S$. Conditional on the revealed information, this crossing edge is independent of the outside path and marks. The outside ghost-connection probability is at most $M_v(h)\leq M^*(h)$, by inclusion in the full graph. A union bound therefore gives conditional probability at most</p>
<div class="math-display">$$e^{-h|S|}\sum_{u\in S}\sum_{\substack{v\notin S\\\{u,v\}\notin E_0}}q(u,v)M^*(h)\leq\delta |S|e^{-h|S|}M^*(h).$$</div>
<p>Sum over the countable family of finite sets $S$. This proves the upper bound. No finite mean for $X$ is needed at positive $h$, since $Xe^{-hX}$ is bounded.</p>
<p>For an intensity model with $q(u,v)=1-e^{-\beta J(u,v)}$, the bound $q(u,v)\leq\beta J(u,v)$ shows that an omitted-kernel row estimate</p>
<div class="math-display">$$\sup_u\sum_{\substack{v\neq u\\\{u,v\}\notin E_r}}J(u,v)\leq C_0r^{-\alpha}$$</div>
<p>gives the comparison below with $C=\beta C_0$, provided the full law is transitive and the cutoff root cluster is almost surely finite. This proves the omitted-edge step in the notes, lines 5247–5273. The last-exit choice makes the remaining path lie entirely in the unconditioned outside graph.</p>

## Adding an independent bond layer {#section-soft-comparison}

<a id="tag-BEJT" data-assertion="proposition" data-title="Ghost comparison for two independent bond layers"></a>
<p>On a countable vertex set, take two mutually independent product bond configurations, called red and blue, with symmetric off-diagonal probabilities $q_0(u,v)$ and $s(u,v)$ in $[0,1]$. Their union has product probabilities $q(u,v)=q_0(u,v)+(1-q_0(u,v))s(u,v)$. Suppose the red root cluster has finite size $X$ almost surely and</p>
<div class="math-display">$$\delta=\sup_u\sum_{v\ne u}s(u,v)&lt;\infty.$$</div>
<p>For independent vertex marks with green probability $1-e^{-h}$, $h&gt;0$, let $G_o(h)$ be the union cluster's ghost probability and $G^*(h)=\sup_vG_v(h)$. Then</p>
<div class="math-display">$$\mathbb E[1-e^{-hX}]\leq G_o(h)\leq\mathbb E[1-e^{-hX}]+\delta\mathbb E[Xe^{-hX}]G^*(h).$$</div>
<p><em>Proof.</em> Condition on the red cluster at the root being the finite set $S$. This reveals no blue bonds, and the red bonds with both endpoints outside $S$ retain their product law. If the union cluster reaches a green vertex while $S$ contains none, take an open path to such a vertex and its last exit from $S$. The crossing bond must be blue, because every red boundary bond is closed. Its blue state is independent of the subsequent path, which lies entirely outside $S$, and of the marks. The conditional union bound is therefore at most</p>
<div class="math-display">$$e^{-h|S|}\sum_{u\in S}\sum_{v\notin S}s(u,v)G^*(h)\leq\delta |S|e^{-h|S|}G^*(h).$$</div>
<p>Average over the countable family of finite sets $S$. The lower bound follows from inclusion of the red cluster in the union cluster. This proof does not require a finite red mean, since $Xe^{-hX}$ is bounded at positive $h$.</p>
<p>For finite nonnegative intensities $J_0\leq J$ and finite $\beta\geq0$, choose $q_0=1-e^{-\beta J_0}$ and $s=1-e^{-\beta(J-J_0)}$. The union then has intensity $\beta J$, and $s\leq\beta(J-J_0)$. Blue bonds may join vertices at distances already present in the red model; the coupling is not restricted to deleting a deterministic set of edges. Under transitivity of the union law, $G^*=G_o$, making the error multiplicative.</p>

<a id="tag-C4E9" data-assertion="proposition" data-title="The added layer of a soft power-law cutoff has a small probability row"></a>
<p>Let $d\geq1$, $\alpha,A&gt;0$, and let $j:[1,\infty)\to[0,\infty)$ be nonincreasing with $j(t)\leq At^{-d-\alpha}$. On $\mathbb Z^d$ use the Euclidean norm and off-diagonal kernels</p>
<div class="math-display">$$J(u,v)=j(\|v-u\|_2),\qquad J_r(u,v)=\mathbf1_{\{\|v-u\|_2\leq r\}}\bigl(j(\|v-u\|_2)-j(r)\bigr),\qquad r\geq1.$$</div>
<p>Then $0\leq J_r\leq J$ and</p>
<div class="math-display">$$\sum_{v\ne u}(J-J_r)(u,v)\leq A3^d\left(1+\frac{2^d}{1-2^{-\alpha}}\right)r^{-\alpha}.$$</div>
<p>Thus the independent added layer at finite intensity $\beta\geq0$ has probability rows bounded by the same expression multiplied by $\beta$. If the cutoff root cluster is almost surely finite, the preceding proposition gives a multiplicative ghost comparison with a constant times $r^{-\alpha}$.</p>
<p><em>Proof.</em> Translation reduces the row to the root. Inside $B_r\setminus\{0\}$, the difference of kernels is $j(r)$; outside $B_r$ it is $j(\|v\|_2)$. Since $|B_t|\leq(2t+1)^d\leq3^dt^d$ for $t\geq1$, the inside contribution is at most $A3^dr^{-\alpha}$. On the annulus $2^kr&lt;\|v\|_2\leq2^{k+1}r$, the contribution is at most $A3^d2^dr^{-\alpha}2^{-k\alpha}$. Sum this geometric series over $k\geq0$ and use $1-e^{-x}\leq x$ for the probability row.</p>
<p>The bound excludes diagonal pairs. Almost-sure finiteness of the cutoff cluster is still needed for the ghost comparison; a finite interaction range alone does not imply it. For the normalized power-law soft cutoff, <a href="/tag/0CUF/">strict domination below the full endpoint</a> supplies finiteness under its stated susceptibility hypothesis. No differentiability of $j$ is needed for this row estimate.</p>

## A conditional cutoff-to-full transfer {#section-full-transfer}

<a id="tag-9PSJ" data-assertion="theorem" data-title="Full tail asymptotics from a multiplicative cutoff comparison"></a>
<p>Let $\alpha&gt;0$, $a&gt;1$, and $A_1,A_2&gt;0$. Let $f$ be positive, continuous, strictly increasing and unbounded for sufficiently large arguments, and regularly varying with index $a\alpha$; write $F=f^{-1}$. Suppose $X_r\geq0$ has finite first and second moments with</p>
<div class="math-display">$$m_r=\mathbb E X_r\sim A_1r^\alpha,\qquad b_r=\frac{\mathbb E X_r^2}{m_r}\sim A_2f(r).$$</div>
<p>Suppose the law $Q_r$ of $X_r/b_r$ under size bias converges weakly to a probability law $Q$ on $[0,\infty)$ with $Q(\{0\})=0$. Let $T\in[0,\infty]$, and put $M(h)=\mathbb E[1-e^{-hT}]$ and $M_r(h)=\mathbb E[1-e^{-hX_r}]$ for $h&gt;0$, with $e^{-h\infty}=0$. Assume there are $C&lt;\infty$, $C\geq0$, $r_0$ and $h_0&gt;0$ such that</p>
<div class="math-display">$$M_r(h)\leq M(h)\leq M_r(h)+Cr^{-\alpha}\mathbb E[X_re^{-hX_r}]M(h)\qquad(r\geq r_0,\ 0&lt;h&lt;h_0).$$</div>
<p>Then the following limit exists and belongs to $(0,\infty)$:</p>
<div class="math-display">$$c_* = A_1A_2^{-1/a}\lim_{\lambda\to\infty}\lambda^{1/a-1}\int_{[0,\infty)}\frac{1-e^{-\lambda y}}y\,dQ(y).$$</div>
<p>Moreover, $T$ is finite almost surely and</p>
<div class="math-display">$$M(h)\sim c_*hF(1/h)^\alpha\quad(h\downarrow0),\qquad \mathbb P(T&gt;t)\sim\frac{c_*}{\Gamma(1/a)}\frac{F(t)^\alpha}{t}\quad(t\to\infty).$$</div>
<p>For integer-valued $T$, the same equivalent holds with $\mathbb P(T\geq n)$. If $a=2$ and $Q$ is the law of $N^2$, then $c_*=A_1\sqrt{2/A_2}$.</p>
<p><em>Proof.</em> The inverse $F$ is regularly varying with index $1/(a\alpha)$. Indeed, for a fixed $c&gt;0$, compare $f(dx)/f(x)$ and $f(ex)/f(x)$ with $c$, where $d&lt;c^{1/(a\alpha)}&lt;e$, then apply monotonicity to squeeze $F(cf(x))/x$ between $d$ and $e$.</p>
<p>Fix $\lambda&gt;0$ and choose $r=F(\lambda/(A_2h))$. Then $hb_r\to\lambda$. Set $g(h)=hF(1/h)^\alpha$. The fixed-scale ghost-transform limit above and regular variation give</p>
<div class="math-display">$$\frac{M_r(h)}{g(h)}\longrightarrow c_\lambda:=A_1A_2^{-1/a}\lambda^{1/a-1}\int\frac{1-e^{-\lambda y}}y\,dQ(y)\in(0,\infty).$$</div>
<p>The comparison error has a separate limit:</p>
<div class="math-display">$$Cr^{-\alpha}\mathbb E[X_re^{-hX_r}]=Cr^{-\alpha}m_r\int e^{-hb_ry}\,dQ_r(y)\longrightarrow\varepsilon_\lambda:=CA_1\int e^{-\lambda y}\,dQ(y).$$</div>
<p>Weak convergence applies here to the bounded continuous exponential. Replacing $hb_r$ by $\lambda$ causes a uniformly vanishing error, since $\sup_{y\geq0}y e^{-\lambda y/2}&lt;\infty$. Also $\varepsilon_\lambda\to0$ as $\lambda\to\infty$, because $Q$ has no atom at zero.</p>
<p>Let $L=\liminf_{h\downarrow0}M(h)/g(h)$ and $U=\limsup_{h\downarrow0}M(h)/g(h)$. For each sufficiently large fixed $\lambda$, rearranging the comparison and then sending $h$ to zero gives</p>
<div class="math-display">$$0&lt;c_\lambda\leq L\leq U\leq\frac{c_\lambda}{1-\varepsilon_\lambda}&lt;\infty.$$</div>
<p>In particular $0&lt;L\leq U&lt;\infty$, and $U/L\leq(1-\varepsilon_\lambda)^{-1}$ for every such $\lambda$. Letting $\lambda\to\infty$ gives $L=U=:c_*$. The same inequalities squeeze $c_\lambda$ between $(1-\varepsilon_\lambda)c_*$ and $c_*$, proving the asserted limit formula. This keeps the two limits in their required order; no uniform weak-convergence assertion in $\lambda$ is used.</p>
<p>Now $g(h)$ is regularly varying at zero with index $\rho=1-1/a\in(0,1)$, so $g(h)\to0$. The <a href="#/ghost-fields">zero-field limit</a> gives $\mathbb P(T=\infty)=0$. Apply the <a href="#/regular-variation">Laplace–tail theorem</a> with index $\rho$, for which $\Gamma(1-\rho)=\Gamma(1/a)$, to obtain the tail equivalent. Rounding does not change it for integer-valued $T$. For $a=2$ and $Q=N^2$, the integral is $\sqrt{1+2\lambda}-1$, giving the stated constant.</p>
<p>This proves the analytic transfer behind the notes' S034 under an explicit cutoff-comparison hypothesis, in the fractional-tail range $a&gt;1$ and with an eventually invertible scale. For independent percolation, the preceding omitted-edge lemma supplies that comparison once a uniform omitted-kernel row bound and almost-sure finiteness of the cutoff root cluster are established. The small-scale information about $Q$ is obtained from the comparison, rather than assumed to follow from weak convergence alone.</p>

## The full tail for the normalized high-dimensional model {#section-normalized-tail}

<a id="tag-26NT" data-assertion="theorem" data-title="Cutoff moments give the full critical volume-tail equivalent under explicit endpoint assumptions"></a>
<p>Assume the normalized soft-kernel and susceptibility endpoint hypotheses of <a href="/tag/7F5O/">7F5O</a>, in particular $d&gt;3\alpha$. Let $B=\alpha/(b v_d)$, and let $A\in(0,\infty)$ be the second-moment amplitude in <a href="/tag/K3DB/">K3DB</a>. Write $X_r$ for the cutoff root-cluster volume at intensity $b$, and $T$ for the full-model root-cluster volume. Under volume bias by $X_r$,</p>
<div class="math-display">$$\frac{X_r}{\mathbb E X_r^2/\mathbb E X_r}\Longrightarrow N^2,$$</div>
<p>where $N$ is standard normal. Moreover, $T&lt;\infty$ almost surely and</p>
<div class="math-display">$$\mathbb E[1-e^{-hT}]\sim\sqrt{\frac{2B^3}{A}}\,h^{1/2},\qquad\mathbb P(T\geq n)\sim\sqrt{\frac{2B^3}{\pi A}}\,n^{-1/2}.$$</div>
<p>The limits are $h\downarrow0$ and integer $n\to\infty$, respectively.</p>
<p><em>Proof.</em> K3DB gives every fixed cutoff moment equivalent, so <a href="/tag/0N85/">0N85</a> gives the biased limit. Its normalization satisfies $\mathbb E X_r^2/\mathbb E X_r\sim(A/B)r^{2\alpha}$, while $\mathbb E X_r\sim Br^\alpha$.</p>
<p>For this kernel, $j(t)=t^{-d-\alpha}/(d+\alpha)$. The <a href="/tag/C4E9/">omitted-kernel row bound</a> is therefore $O(r^{-\alpha})$. Add an independent layer of intensity $b(J_\infty-J_r)$ to the cutoff model. Its union has exactly the full-model law, and <a href="/tag/BEJT/">BEJT</a> gives the multiplicative ghost comparison required by <a href="/tag/9PSJ/">9PSJ</a>. Cutoff clusters are finite by 0CUF, and translation invariance identifies the supremum of full ghost probabilities with the rooted probability.</p>
<p>Apply 9PSJ with scale function $f(r)=r^{2\alpha}$, exponent parameter $a=2$, $A_1=B$ and $A_2=A/B$. The limiting law $N^2$ has no atom at zero. Its ghost-transform coefficient is $B\sqrt{2/(A/B)}=\sqrt{2B^3/A}$. The theorem gives almost-sure finiteness of $T$ and the tail coefficient after division by $\Gamma(1/2)=\sqrt\pi$.</p>
<p>This assembles the high-dimensional cutoff-to-full argument for the stated normalized model. Almost-sure finiteness at the endpoint is a conclusion; only divergence of its susceptibility was assumed. The endpoint hypotheses themselves remain to be supplied by sharpness and an endpoint-divergence result. No spatial scaling-limit claim follows from this volume law.</p>

## Conditioning a fixed generation {#section-conditioning}

<a id="tag-SBWK" data-assertion="theorem" data-title="Distant survival size-biases a fixed critical generation"></a><p>For each fixed $r$ and each bounded $\mathcal F_r$-measurable random variable $F$,</p><div class="math-display">$$\lim_{R\to\infty}\mathbb E[F\mid Z_R&gt;0]=\mathbb E[FZ_r].$$</div><p>Consequently, the limiting distribution of $Z_r$ assigns probability $k\mathbb P(Z_r=k)$ to $k$. It is normalized because $\mathbb E Z_r=1$.</p><p><em>Proof.</em> Write $Q_n=\mathbb P(Z_n&gt;0)$. The branching property gives</p><div class="math-display">$$\mathbb P(Z_R&gt;0\mid\mathcal F_r)=1-(1-Q_{R-r})^{Z_r}.$$</div><p>By the <a href="/tag/8WO7/">critical survival asymptotic</a>, $Q_n\sim2/(\sigma^2 n)$. Hence $Q_{R-r}/Q_R\to1$, and for each finite integer $k$,</p><div class="math-display">$$\frac{1-(1-Q_{R-r})^k}{Q_R}\longrightarrow k.$$</div><p>The numerator is at most $kQ_{R-r}$, so for all sufficiently large $R$ the random ratio is bounded by $2Z_r$. Since $\mathbb E Z_r=1$, dominated convergence applied after multiplication by $F$ proves the claim.</p>

<a id="tag-XCA8" data-assertion="proposition" data-title="Consistency of the size-biased tree restrictions"></a><p>The probability laws $\widehat{\mathbb P}_r(A)=\mathbb E[Z_r\mathbf1_A]$, $A\in\mathcal F_r$, are consistent as $r$ varies: for $s\leq r$ and $A\in\mathcal F_s$,</p><div class="math-display">$$\widehat{\mathbb P}_r(A)=\widehat{\mathbb P}_s(A).$$</div><p><em>Proof.</em> Criticality gives $\mathbb E[Z_r\mid\mathcal F_s]=Z_s$. Taking expectations after multiplication by $\mathbf1_A$ gives the equality.</p><p>These are the finite-generation laws of the incipient infinite critical tree. They assign probability one to $Z_r&gt;0$ at every fixed level. This statement concerns the branching-process tree; it does not assert existence of a conditioning limit for percolation on a Euclidean lattice.</p>

## Constructing the infinite spine {#section-spine}

<a id="tag-RMFH" data-assertion="theorem" data-title="Spine construction of the critical size-biased tree"></a>
<p>Let $\mu$ be a nondegenerate critical offspring law with finite nonzero variance. Order each individual's children from $1$ to its offspring count. Construct a marked tree with an infinite distinguished line as follows. Independently at each vertex on that line, choose $k$ children with probability $\widehat\mu(k)=k\mu(k)$ and choose one of them uniformly to continue the line. Attach independent ordinary Galton–Watson trees with law $\mu$ to all other children.</p>
<p>After forgetting the distinguished line, the tree through generation $r$ has law</p>
<div class="math-display">$$\widehat{\mathbb P}(A)=\mathbb E[Z_r\mathbf1_A]\qquad(A\in\mathcal F_r).$$</div>
<p>Thus this constructs the consistent law of <a href="/tag/XCA8/">XCA8</a> on an infinite tree. Almost surely the distinguished line is its unique infinite ray from the root.</p>
<p><em>Proof.</em> Criticality makes $\widehat\mu$ a probability law, supported on positive finite integers. Fix an ordered tree $t$ through level $r$ and a vertex $v$ at that level. For each vertex of the root-to-$v$ line with $k$ children, choosing those children and the prescribed next child contributes $k\mu(k)/k=\mu(k)$. Every other vertex below level $r$ contributes the ordinary factor $\mu(k)$. Consequently the probability of $(t,v)$ is exactly the ordinary probability of $t$. Summing over its $Z_r(t)$ possible marked vertices gives the displayed size-biased law. These finite trees form a countable set, so the identity extends to every event in $\mathcal F_r$.</p>
<p>The construction uses countably many independent choices and produces finite offspring at every vertex. Every ordinary tree grafted to the spine is finite almost surely by critical nondegenerate extinction. There are only countably many such grafts, so they are all finite simultaneously almost surely. Any ray that left the spine would stay in one of them and terminate. The spine is therefore the only infinite ray.</p>

## Observing a growing prefix {#section-growing-prefix}

<a id="tag-SYJ4" data-assertion="proposition" data-title="Total-variation approximation by the spine law below a distant survival horizon"></a>
<p>For the same critical process, put $Q_k=\mathbb P(Z_k&gt;0)$. Let $P_{r,R}$ be the law on $\mathcal F_r$ conditional on $Z_R&gt;0$, where $0\leq r\leq R$, and let $\widehat P_r$ be the spine restriction. With total variation defined by $\|P-Q\|_{\rm TV}=\sup_A|P(A)-Q(A)|$,</p>
<div class="math-display">$$\|P_{r,R}-\widehat P_r\|_{\rm TV}
\leq1-\frac{Q_R}{Q_{R-r}}.$$</div>
<p>In particular this distance tends to zero whenever $R\to\infty$ and $r=r_R=o(R)$. The approximation concerns the entire tree prefix, not only its population.</p>
<p><em>Proof.</em> Relative to the ordinary law on $\mathcal F_r$, the conditional density is</p>
<div class="math-display">$$D_{r,R}=\frac{1-(1-Q_{R-r})^{Z_r}}{Q_R}
\leq\frac{Q_{R-r}}{Q_R}Z_r.$$</div>
<p>The spine density is $Z_r$. Thus, with $\eta=Q_R/Q_{R-r}\in(0,1]$, the measure $\widehat P_r-\eta P_{r,R}$ is nonnegative and has mass $1-\eta$. If $\eta&lt;1$, normalizing this remainder writes $\widehat P_r$ as a mixture of $P_{r,R}$ with weight $\eta$ and another probability law. This proves the total-variation bound; when $\eta=1$ the measures coincide. Finally <a href="/tag/8WO7/">$Q_k\sim2/(\sigma^2k)$</a> gives $Q_R/Q_{R-r}\to1$ for $r=o(R)$.</p>
<p>This strengthens the fixed-generation conclusion SBWK without interchanging two unproved limits. The displayed ratio is the error bound; no uniform rate for its asymptotic approximation is asserted.</p>

## Expected mass after conditioning {#section-mass}

<a id="tag-JNOW" data-assertion="proposition" data-title="Generation and ball means under critical tree size bias"></a><p>The original critical process satisfies $\mathbb E Z_r^2=1+r\sigma^2$. Under the consistent size-biased restrictions,</p><div class="math-display">$$\widehat{\mathbb E}Z_r=1+r\sigma^2,\qquad \widehat{\mathbb E}\!\left[\sum_{k=0}^{r}Z_k\right]=(r+1)+\frac{\sigma^2r(r+1)}2.$$</div><p>For critical percolation on the rooted binary tree, $\sigma^2=1/2$, giving generation mean $1+r/2$ and ball mean $(r+1)+r(r+1)/4$.</p><p><em>Proof.</em> Given $Z_r$, the next population is a sum of $Z_r$ independent offspring counts, with conditional mean $Z_r$ and variance $\sigma^2Z_r$. Therefore</p><div class="math-display">$$\mathbb E[Z_{r+1}^2\mid\mathcal F_r]=Z_r^2+\sigma^2Z_r.$$</div><p>Taking expectations and using $\mathbb E Z_r=1$ proves the second-moment formula by induction. Size bias at level $r$ gives $\widehat{\mathbb E}Z_r=\mathbb E Z_r^2$. Consistency gives the corresponding mean at every earlier level under the same restriction, and summing proves the ball formula.</p>

<p>These expectations are computed under the limiting finite-generation laws. Convergence in distribution alone would not justify passing expectations of unbounded populations through the conditioning limit.</p>

## A finite block conditioned on survival {#section-survival-block}

<a id="tag-4AVL" data-assertion="proposition" data-title="Exact future-generation mass conditioned on critical survival"></a>
<p>Let $(Z_n)$ be a Galton–Watson process started from one individual with offspring mean one, and put $Q_r=\mathbb P(Z_r&gt;0)$. For integers $0\leq r\leq a\leq b$,</p>
<div class="math-display">$$\mathbb E\!\left[\sum_{n=a}^{b}Z_n\,\middle|\,Z_r&gt;0\right]=\frac{b-a+1}{Q_r}.$$</div>
<p>In particular, for $r\geq1$, the expected mass in generations $r+1,\ldots,2r$, conditional on survival to generation $r$, is exactly $r/Q_r$. If the offspring variance satisfies $0&lt;\sigma^2&lt;\infty$, then</p>
<div class="math-display">$$\mathbb E\!\left[\sum_{n=r+1}^{2r}Z_n\,\middle|\,Z_r&gt;0\right]\sim\frac{\sigma^2}{2}r^2\qquad(r\to\infty).$$</div>
<p><em>Proof.</em> Criticality gives $\mathbb E Z_n=1$ for every $n$, so $Q_r&gt;0$. Extinction is absorbing: for $n\geq r$, $Z_n\mathbf1_{\{Z_r&gt;0\}}=Z_n$. Sum this identity from $a$ to $b$, take expectations and divide by $Q_r$. The asymptotic follows from $Q_r\sim2/(\sigma^2r)$.</p>
<p>On the critical rooted binary tree, $\sigma^2=1/2$, so the block mean is asymptotic to $r^2/4$. This strengthens the inequality in the <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L760">notes' finite-survival calculation</a> to equality. It concerns conditioning at level $r$, not the limit obtained by sending the conditioning level to infinity first. Nor does an expected mass estimate alone prove concentration or a typical diameter. The exact identity needs no second moment; for deterministic one-child reproduction it gives the block mass $r$, and the quadratic asymptotic does not apply.</p>

## Population laws for different conditioning horizons {#section-population-horizons}

<a id="tag-OBSY" data-assertion="theorem" data-title="Critical population limits under comparable and distant survival conditioning"></a>
<p>Let the critical offspring variance be $\sigma^2\in(0,\infty)$ and put $a=\sigma^2/2$. Under the spine law,</p>
<div class="math-display">$$\frac{Z_n}{n}\ \Longrightarrow\ E_1+E_2,$$</div>
<p>where $E_1,E_2$ are independent exponential variables of mean $a$. More generally, let integers $R_n\geq n$ satisfy $R_n/n\to c\in[1,\infty]$. Then</p>
<div class="math-display">$$\operatorname{Law}\left(\frac{Z_n}{n}\,\middle|\,Z_{R_n}&gt;0\right)
\ \Longrightarrow\ \operatorname{Law}\left(E_1+(1-c^{-1})E_2\right),$$</div>
<p>where $c^{-1}=0$ if $c=\infty$. At $c=1$ the limit is the exponential law of Yaglom's theorem. At $c=\infty$ it has density $x a^{-2}e^{-x/a}$ on $x&gt;0$, the size-biased exponential law.</p>
<p><em>Proof.</em> Write $Y_n=Z_n/n$. By <a href="/tag/AYHV/">AYHV</a>, its conditional law given $Z_n&gt;0$ converges to an exponential variable $Y$ of mean $a$, and these conditional laws are uniformly integrable. For bounded continuous $f$, the spine identity gives</p>
<div class="math-display">$$\widehat{\mathbb E}f(Z_n/n)
=nQ_n\,\mathbb E[Y_nf(Y_n)\mid Z_n&gt;0]
\longrightarrow\frac1a\mathbb E[Yf(Y)].$$</div>
<p>Uniform integrability justifies testing by $y f(y)$, and $nQ_n\to1/a$. Size-biasing the exponential density gives $x a^{-2}e^{-x/a}$, the convolution of two mean-$a$ exponential laws. This proves the spine limit.</p>
<p>For finite $c&gt;1$, set $q_n=Q_{R_n-n}$. The branching property gives</p>
<div class="math-display">$$\mathbb E[f(Z_n/n)\mid Z_{R_n}&gt;0]
=\frac{Q_n}{Q_{R_n}}\,
\mathbb E\!\left[f(Y_n)\{1-(1-q_n)^{nY_n}\}\,\middle|\,Z_n&gt;0\right].$$</div>
<p>Now $Q_n/Q_{R_n}\to c$ and $nq_n\to1/[a(c-1)]$. The factor in braces therefore tends, uniformly on compact $y$-intervals, to $1-e^{-y/[a(c-1)]}$. It is bounded by one, so weak convergence and tightness give the limiting density</p>
<div class="math-display">$$\frac ca\left(e^{-x/a}-e^{-cx/[a(c-1)]}\right)\qquad(x&gt;0).$$</div>
<p>This is the convolution density of exponentials with means $a$ and $a(1-1/c)$, respectively, proving the asserted representation and its normalization.</p>
<p>If $c=1$, then $R_n-n=o(n)$ and $nQ_{R_n-n}\to\infty$. This follows from the survival asymptotic when $R_n-n\to\infty$, and from positivity of each fixed-generation survival probability on bounded subsequences. Hence the factor in braces tends to one uniformly for $y\geq\varepsilon&gt;0$. The exponential limit has no atom at zero, while $Q_n/Q_{R_n}\to1$; the same expectation identity gives the Yaglom limit. If $c=\infty$, apply <a href="/tag/SYJ4/">SYJ4</a> with $r=n=o(R_n)$. Total variation cannot increase under the map taking the prefix to $Z_n/n$, so the conditional and spine laws have the same limit.</p>
<p>The comparable-horizon law retains the finite conditioning horizon. Sending that horizon much farther than the observed generation gives the spine law, including for growing observed generations. These are population limits for the critical branching tree; no spatial or Euclidean IIC limit is asserted.</p>

## Mixed moments of an embedded cluster {#section-embedded-measures}

<a id="tag-XA7C" data-assertion="proposition" data-title="Rescaled cluster measures under volume size bias"></a>
<p>Let $K$ be a random subset of a countable $V\subseteq\mathbb R^d$, with $0&lt;\chi=\mathbb E|K|&lt;\infty$. For finite constants $s,\zeta&gt;0$, define the random finite measure and the volume-biased probability law by</p>
<div class="math-display">$$\mu=\frac1\zeta\sum_{x\in K}\delta_{x/s},\qquad \frac{d\mathbb Q}{d\mathbb P}=\frac{|K|}{\chi}.$$</div>
<p>For bounded nonnegative Borel functions $f_1,\ldots,f_k$, $k\geq1$, write $\langle\mu,f\rangle=\int f\,d\mu$. Then, with nonnegative extended expectations,</p>
<div class="math-display">$$\begin{aligned}
\mathbb E\prod_{j=1}^k\langle\mu,f_j\rangle
&=\frac1{\zeta^k}\sum_{x_1,\ldots,x_k\in V}\left[\prod_{j=1}^k f_j(x_j/s)\right]\mathbb P(x_1,\ldots,x_k\in K),\\
\mathbb E_{\mathbb Q}\prod_{j=1}^k\langle\mu,f_j\rangle
&=\frac1{\chi\zeta^k}\sum_{y,x_1,\ldots,x_k\in V}\left[\prod_{j=1}^k f_j(x_j/s)\right]\mathbb P(y,x_1,\ldots,x_k\in K).
\end{aligned}$$</div>
<p>If $\mathbb E|K|^2&lt;\infty$ and $\zeta=\mathbb E|K|^2/\chi$, then $\mathbb E_{\mathbb Q}\mu(\mathbb R^d)=1$.</p>
<p><em>Proof.</em> Finite mean makes $K$ finite almost surely, and the displayed density integrates to one. Expand the product of the finite sums defining the integrals and apply Tonelli. For the second formula multiply by $|K|/\chi=\chi^{-1}\sum_y\mathbf1_{\{y\in K\}}$ before taking expectation. Repeated vertices are allowed; products of their indicators still express simultaneous membership. Taking $k=1$ and $f_1=1$ gives the final assertion.</p>
<p>When $K=K_o$ is a percolation cluster, the probabilities in these sums are multipoint connections including $o$. Thus convergence of embedded-cluster mixed moments requires spatially weighted multipoint information, beyond the scalar moments obtained by setting every $f_j=1$. The mean-one normalization is under $\mathbb Q$, not under the original law.</p>

<a id="tag-WGQ7" data-assertion="proposition" data-title="Fixed total mass does not prevent spatial escape"></a>
<p>On $\mathbb R^d$, $d\geq1$, the deterministic measures $\nu_n=\delta_{ne_1}$ have total mass one and hence identical total-mass moments of every order. Nevertheless, no subsequence converges weakly as finite measures, where weak convergence tests all bounded continuous functions.</p>
<p><em>Proof.</em> Along any subsequence tending to infinity, every compactly supported continuous test function has integral eventually zero. If a weak limit $\nu$ existed, choose such a nonnegative function equal to one on each prescribed closed ball. Its zero integral would imply that $\nu$ assigns zero mass to that ball, hence to all of $\mathbb R^d$. But the bounded continuous test function $1$ would give $\nu(\mathbb R^d)=1$, a contradiction.</p>
<p>The same sequence does converge vaguely to zero, since vague convergence uses compactly supported tests. This example concerns finite measures, not percolation clusters; it isolates the spatial tightness issue that scalar volume moments cannot resolve.</p>
<p>The <a href="https://github.com/tomhutchcroft/lrp/blob/7a303901b9e4708259bf74ca2333c0515a784af8/sources/notes/book_draft.tex#L4399">notes' superprocess discussion</a> uses precisely the size-biased volume scale in the first proposition. These identities explain that normalization but do not identify a limiting random measure. Spatial tightness, the chosen topology, convergence and determination by mixed moments, and passage from size bias to conditioning on a large full cluster remain separate requirements. No stable or Brownian superprocess limit is asserted here.</p>

## From polynomial diagrams to a random-measure limit {#section-measure-convergence}

<a id="tag-Y3SX" data-assertion="theorem" data-title="Polynomial tree-moment asymptotics determine the size-biased random-measure limit"></a>
<p>For each integer $j\geq1$, let $K_j$ be a random finite nonempty subset of a countable subset of $\mathbb R^d$, with $0&lt;\chi_j=\mathbb E|K_j|&lt;\infty$. Let $s_j,z_j&gt;0$, and put</p>
<div class="math-display">$$\mu_j=z_j^{-1}\sum_{x\in K_j}\delta_{x/s_j},\qquad\frac{d\mathbb Q_j}{d\mathbb P_j}=\frac{|K_j|}{\chi_j}.$$</div>
<p>Use the kernel and diagrams of <a href="/tag/GFEM/">GFEM</a>. Suppose that for every $n\geq1$ and real polynomials $P_1,\ldots,P_n$, the following expectations are absolutely integrable and</p>
<div class="math-display">$$\frac{\mathbb E\left[\sum_{x_1,\ldots,x_n\in K_j}\prod_{i=1}^nP_i(x_i/s_j)\right]}{\chi_j z_j^{n-1}}\longrightarrow D_n(P_1,\ldots,P_n).$$</div>
<p>Then the laws of $\mu_j$ under $\mathbb Q_j$ converge weakly on the space of finite Borel measures on $\mathbb R^d$, equipped with weak convergence against bounded continuous functions. The limit law is uniquely determined by the diagrams. If $\mu$ has that law, then for every $k\geq1$ and bounded continuous $f_1,\ldots,f_k$,</p>
<div class="math-display">$$\mathbb E\prod_{i=1}^k\langle\mu,f_i\rangle=D_{k+1}(f_1,\ldots,f_k,1).$$</div>
<p>Here the right side uses the same finite tree integrals, which are well-defined for bounded functions. The total mass $\mu(\mathbb R^d)$ has the squared-standard-normal law.</p>
<p><em>Proof.</em> Size bias inserts one extra marked vertex, as in <a href="/tag/XA7C/">XA7C</a>. Thus the $k$th moment measure $M_j^{(k)}=\mathbb E_{\mathbb Q_j}\mu_j^{\otimes k}$ has polynomial moments converging to those of the finite measure $M^{(k)}$ defined by $D_{k+1}(f_1,\ldots,f_k,1)$. Its total mass tends to $(2k-1)!!$.</p>
<p>For each fixed $k$, convergence of second spatial moments makes the family $M_j^{(k)}$ tight on $(\mathbb R^d)^k$. Higher even moments make every fixed polynomial uniformly integrable. Hence any weak subsequential limit has exactly the polynomial moments of $M^{(k)}$. By GFEM the latter has an exponential moment of the Euclidean norm near zero, so its moments determine it: every linear projection has a moment generating function near zero, with coefficients fixed by its moments, and the one-dimensional uniqueness theorem followed by Cramér–Wold identifies the finite measure after normalization. The same exponential integrability for a competitor follows by summing its even moments. It follows that $M_j^{(k)}\Rightarrow M^{(k)}$.</p>
<p>The laws of the random measures themselves are tight. Indeed, $M_j^{(1)}$ have uniformly bounded mass and uniformly vanishing mass outside large balls. Given $\eta&gt;0$, choose a mass bound $B$ and radii $R_\ell\uparrow\infty$ so that</p>
<div class="math-display">$$\sup_j\mathbb Q_j(\mu_j(\mathbb R^d)&gt;B)&lt;\eta/2,\qquad \sup_j\mathbb E_{\mathbb Q_j}\mu_j(B_{R_\ell}^c)\leq\eta 2^{-2\ell-2}.$$</div>
<p>Markov's inequality and a union bound show that, for every $j$, the measure $\mu_j$ belongs with $\mathbb Q_j$-probability at least $1-\eta$ to the same collection: measures of mass at most $B$ whose mass outside $B_{R_\ell}$ is at most $2^{-\ell}$ for every $\ell\geq1$. This collection is uniformly tight and bounded, so its closure is compact for weak convergence. Prokhorov's theorem gives tightness of the laws.</p>
<p>Take a subsequential random-measure limit $\mu$. The total-mass moment of order $k+1$ is bounded along the sequence. Therefore products of $k$ bounded continuous integrals are uniformly integrable, and their expectations converge to those of $\mu$. The already established convergence of $M_j^{(k)}$ gives the displayed identity. In particular, the total-mass moments are $(2k-1)!!$. Tonelli and the binomial series give</p>
<div class="math-display">$$\mathbb E e^{t\mu(\mathbb R^d)}=\sum_{k\geq0}\frac{(2k-1)!!}{k!}t^k=(1-2t)^{-1/2}\qquad(0\leq t&lt;1/2),$$</div>
<p>which identifies the squared-normal law. For any finite list of bounded continuous functions, the absolute value of every linear combination of their integrals is bounded by a constant times the total mass. Its moment generating function therefore exists near zero, and the joint moments determine its joint law. A countable collection of bounded continuous test functions separating finite measures, including the constant function one, determines the Borel law on this measure space. All subsequential limits coincide, proving convergence of the full sequence.</p>
<p>For cutoff clusters the conventional choice is $z_j=\mathbb E|K_j|^2/\chi_j$. The theorem explains why the diagram with $k+1$ marked vertices, rather than $k$, gives the $k$th moment under size bias. It also supplies the spatial tightness step missing from a volume-only argument. The hypothesis is convergence for every polynomial mixed moment; a second-moment spatial scale alone does not supply it. Applying the sequential statement along every sequence of radii tending to infinity gives the corresponding continuous-scale conclusion.</p>

## The mass mixture behind the reduced genealogy {#section-reduced-tree-mixture}

<a id="tag-45EB" data-assertion="proposition" data-title="Chi-square mass mixing turns reduced-tree lengths into independent exponentials"></a>
<p>Let $m\geq1$ be an integer. Let $A$ and $B$ be independent chi random variables with $m$ and $m+1$ degrees of freedom, respectively, and let $U=(U_1,\ldots,U_m)$ be independent of them and uniform on the simplex $\{u_i\geq0:\sum_i u_i=1\}$. Then $AB$ has the gamma law of shape $m$ and rate one, and $ABU_1,\ldots,ABU_m$ are independent rate-one exponentials.</p>
<p><em>Proof.</em> For every integer $k\geq0$, the chi moments and the gamma duplication formula give</p>
<div class="math-display">$$\mathbb E(AB)^k=2^k\frac{\Gamma((m+k)/2)\Gamma((m+1+k)/2)}{\Gamma(m/2)\Gamma((m+1)/2)}=\frac{\Gamma(m+k)}{\Gamma(m)}.$$</div>
<p>Tonelli now gives $\mathbb E e^{tAB}=(1-t)^{-m}$ for $0\leq t&lt;1$, identifying the gamma law. For $m&gt;1$, transform from the total length $l$ and the first $m-1$ simplex coordinates to the $m$ lengths. The Jacobian is $l^{m-1}$; it cancels the gamma density's power, while the simplex density $(m-1)!$ cancels its normalization. The joint density is $e^{-\sum_i l_i}$ on the positive orthant. For $m=1$ the assertion is just the exponential law of $AB$.</p>
<p>Here is the precise input needed to apply this calculation to the continuum random tree. For the convention encoded by twice a unit-duration Brownian excursion, assume the standard unit-mass reduced-tree law: sampling $n$ independent mass-uniform points and adjoining the root gives a uniform shape in $\mathbb T_n$, independent of a total length with chi distribution of $m+1$ degrees of freedom, where $m=2n-1$; its edge proportions are independent and uniform on the simplex. This geometric fact is a cited input, not proved by the gamma calculation. Also use the scaling rule that multiplying mass by $a$ multiplies lengths by $\sqrt a$.</p>
<p>Sample the unit-mass tree independently of a total mass with the chi-square law with one degree of freedom, and rescale it by that mass. Weighting its probability law by mass to the power $n-1$ and renormalizing gives the chi-square law with $2n-1=m$ degrees of freedom, directly from its density. The calculation above then gives independent exponential reduced-edge lengths. Assigning independent Lévy motion along those edges yields independent endpoint increments with the probability kernel of the motion stopped at an exponential time.</p>
<p>Consequently, if the corresponding tree-indexed occupation measure $\nu$ is constructed, it satisfies</p>
<div class="math-display">$$\mathbb E\left[\frac1{\nu(\mathbb R^d)}\prod_{i=1}^n\langle\nu,P_i\rangle\right]=D_n(P_1,\ldots,P_n).$$</div>
<p>To check the normalization, condition on the tree and sample $n$ independent mass-uniform points. The expression on the left weights their product by mass to the power $n-1$. The mean of that weight is $(2n-3)!!$, exactly the number of shapes; it cancels the uniform shape probability. GFEM then gives the right side. Setting one polynomial equal to one recovers the ordinary moment measures in Y3SX, so its limiting law is this occupation-measure law whenever the geometric input and construction have been supplied.</p>
<p>This separates the algebraic mass mixture from the geometric theorem used in <a href="https://arxiv.org/html/2508.18807v1">Critical LRP I</a>, Theorem I.5.24 and Corollary I.5.22. The percolation mixed-moment asymptotics, the unit-mass reduced-tree law, and construction of the tree-indexed motion remain distinct inputs. The cutoff result does not by itself remove the cutoff or identify the full critical cluster under a large-volume conditioning.</p>

## Controlling the mass added beyond a cutoff {#section-added-mass}

<a id="tag-AYPN" data-assertion="proposition" data-title="Ghost bound for the mass gained from an independent layer"></a>
<p>Let $\omega$ and $\xi$ be independent bond percolation configurations on a countable vertex set. Write $C=K_o(\omega)$, $K^+=K_o(\omega\cup\xi)$ and $D=K^+\setminus C$, and assume $C$ is finite almost surely. Suppose the added-edge probabilities satisfy $\sup_x\sum_{y\ne x}\mathbb P(\{x,y\}\in\xi)\leq a$. For $h&gt;0$, put</p>
<div class="math-display">$$M^*(h)=\sup_v\mathbb E[1-e^{-h|K_v(\omega\cup\xi)|}].$$</div>
<p>With $e^{-h\infty}=0$,</p>
<div class="math-display">$$\mathbb E[1-e^{-h|D|}\mid C]\leq\min\{1,aM^*(h)|C|\}.$$</div>
<p>Consequently, for $t&gt;0$,</p>
<div class="math-display">$$\mathbb P(|D|\geq t)\leq\frac{\mathbb E\min\{1,aM^*(h)|C|\}}{1-e^{-ht}}.$$</div>
<p><em>Proof.</em> Mark vertices independently with probability $1-e^{-h}$, independently of both bond configurations. The probability that the marks meet $D$, conditional on the bonds, is $1-e^{-h|D|}$. Conditional on $C$, the old boundary edges of $C$ are closed, while the old edges with both endpoints outside $C$ retain their independent product law. All added edges retain their original law.</p>
<p>If a marked vertex lies in $D$, choose an open path to it from $o$ in the union configuration and take its last exit from $C$. That exit uses an added edge $\{x,y\}$, with $x\in C$, and the remaining path stays outside $C$. The exit edge is independent of the outside bonds and marks. The outside connection to a mark has probability at most $M^*(h)$, by adding back the deleted vertices. Sum over the exit edges and use the row bound; the resulting probability is also at most one. This proves the conditional estimate. On $|D|\geq t$, the ghost deficit is at least $1-e^{-ht}$, giving the last inequality.</p>
<p>The last exit is needed: a path may leave and re-enter $C$ before reaching its marked endpoint. This estimate requires no finite full-model susceptibility. Unlike <a href="/tag/BEJT/">BEJT</a>, it does not require $C$ itself to avoid the marks.</p>

<a id="tag-L9YJ" data-assertion="theorem" data-title="A regularly varying volume tail makes omitted cluster mass negligible"></a>
<p>Let $K$ be the root cluster in a transitive independent bond model, with $X=|K|&lt;\infty$ almost surely and $F(t)=\mathbb P(X&gt;t)$ regularly varying with index $-\rho$, where $0&lt;\rho&lt;1$. Let $z_R\to\infty$ and $\eta_R\asymp F(z_R)$. For each $s\geq1$, couple a lower model to this full model by an independent added layer, write $C_{R,s}\subseteq K$ for its root cluster, and let $a_{R,s}$ bound the added-edge probability rows. Suppose that for some nonnegative $b(s)\to0$,</p>
<div class="math-display">$$\limsup_{R\to\infty}a_{R,s}z_R\eta_R\leq b(s)\qquad(s\geq1).$$</div>
<p>Then, for every $\delta&gt;0$,</p>
<div class="math-display">$$\lim_{s\to\infty}\limsup_{R\to\infty}\eta_R^{-1}\mathbb P\bigl(|K\setminus C_{R,s}|\geq\delta z_R\bigr)=0.$$</div>
<p><em>Proof.</em> Set $H(h)=\mathbb E\min\{hX,1\}$. Tail integration gives</p>
<div class="math-display">$$H(1/z)=\frac1z\int_0^z F(t)\,dt\sim\frac{F(z)}{1-\rho}.$$</div>
<p>For completeness, divide by $F(z)$ and substitute $t=uz$. The integrand tends to $u^{-\rho}$ on $0&lt;u\leq1$. A regular-variation bound by a constant times $u^{-\rho-\varepsilon}$, with $\rho+\varepsilon&lt;1$, controls the part with $uz$ above a fixed threshold; the remaining integral is $O(1/[zF(z)])=o(1)$. Dominated convergence gives the equivalent. In particular, $H$ is regularly varying at zero with index $\rho$.</p>
<p>Transitivity identifies $M^*(h)$ with the full root ghost probability, which is at most $H(h)$. Take $h=1/z_R$ in AYPN and use $|C_{R,s}|\leq X$. Since $H(1/z_R)\leq A\eta_R$ for a fixed $A$ and all large $R$,</p>
<div class="math-display">$$\mathbb P(|K\setminus C_{R,s}|\geq\delta z_R)\leq\frac{H(a_{R,s}H(1/z_R))}{1-e^{-\delta}}.$$</div>
<p>Put $b_s=b(s)+s^{-1}$. For each fixed $s$, the argument of $H$ on the right is at most $2Ab_s/z_R$ for all sufficiently large $R$. Regular variation at this fixed multiplier, together with $\eta_R\asymp F(z_R)$, yields</p>
<div class="math-display">$$\limsup_{R\to\infty}\frac{\mathbb P(|K\setminus C_{R,s}|\geq\delta z_R)}{\eta_R}\leq\frac{A'}{1-e^{-\delta}}b_s^\rho,$$</div>
<p>where $A'$ is independent of $s$. Now send $s$ to infinity. There is no interchange of these limits and no assumption of uniform regular variation along a varying multiplier.</p>
<p>For a power-law soft cutoff at radius $q(sR)$, <a href="/tag/C4E9/">C4E9</a> gives $a_{R,s}\leq Cq(sR)^{-\alpha}$. If $z_R\eta_R\leq Cq(R)^\alpha$ and $q$ is regularly varying with index $1/\gamma&gt;0$, the hypothesis follows with $b(s)=C's^{-\alpha/\gamma}$. The fractional full-volume tail and these scale estimates remain hypotheses; this corollary does not establish them for a new model.</p>

## Transferring the limit without size bias {#section-cutoff-removal}

<a id="tag-BB3O" data-assertion="theorem" data-title="Transfer from cutoff laws to a measure finite away from zero mass"></a>
<p>Let $\mathcal M$ be the space of finite nonnegative Borel measures on $\mathbb R^d$, with its weak topology, and write $m(\mu)=\mu(\mathbb R^d)$. Let $\eta_R&gt;0$. Suppose random measures $\mu_R$ and $\nu_{R,s}$ are coupled with $\nu_{R,s}\leq\mu_R$, and assume</p>
<div class="math-display">$$\limsup_{R\to\infty}\eta_R^{-1}\mathbb P(m(\mu_R)\geq b)&lt;\infty\quad(b&gt;0),\qquad
\lim_{s\to\infty}\limsup_{R\to\infty}\eta_R^{-1}\mathbb P(m(\mu_R-\nu_{R,s})&gt;\varepsilon)=0\quad(\varepsilon&gt;0).$$</div>
<p>Let $\mathcal N$ be a Borel measure on $\mathcal M\setminus\{0\}$, finite on each set $\{m\geq b\}$, $b&gt;0$. For every nonnegative Lipschitz function $g$ compactly supported in $(0,\infty)$, suppose the finite measures</p>
<div class="math-display">$$\eta_R^{-1}\mathbb E\bigl[g(m(\nu_{R,s}))\mathbf1_{\{\nu_{R,s}\in\cdot\}}\bigr]\Longrightarrow\mathcal N_s^g\quad(R\to\infty),\qquad
\mathcal N_s^g\Longrightarrow g(m)\mathcal N\quad(s\to\infty)$$</div>
<p>converge weakly, with the first limit taken for every fixed $s$. Then</p>
<div class="math-display">$$\eta_R^{-1}\mathbb E\bigl[g(m(\mu_R))\mathbf1_{\{\mu_R\in\cdot\}}\bigr]\Longrightarrow g(m)\mathcal N.$$</div>
<p>If, in addition,</p>
<div class="math-display">$$\lim_{B\to\infty}\limsup_{R\to\infty}\eta_R^{-1}\mathbb P(m(\mu_R)\geq B)=0,$$</div>
<p>then for each $a&gt;0$ with $\mathcal N(m=a)=0$ and $0&lt;\mathcal N(m\geq a)&lt;\infty$,</p>
<div class="math-display">$$\eta_R^{-1}\mathbb P(m(\mu_R)\geq a)\longrightarrow\mathcal N(m\geq a),\qquad
\operatorname{Law}(\mu_R\mid m(\mu_R)\geq a)\Longrightarrow\frac{\mathbf1_{\{m\geq a\}}\mathcal N}{\mathcal N(m\geq a)}.$$</div>
<p><em>Proof.</em> Equip $\mathcal M$ with the bounded-Lipschitz metric $d_{\rm BL}$ obtained by taking the supremum over spatial functions with supremum norm and Lipschitz constant at most one. It metrizes weak convergence, $|m(\mu)-m(\nu)|\leq d_{\rm BL}(\mu,\nu)$, and for $\nu\leq\mu$ we have $d_{\rm BL}(\mu,\nu)\leq m(\mu-\nu)$.</p>
<p>Fix a bounded Lipschitz function $F$ on $\mathcal M$. The function $f(\mu)=g(m(\mu))F(\mu)$ is bounded and Lipschitz; choose $b&gt;0$ such that $g$ vanishes below $b$. Whenever either $f(\mu_R)$ or $f(\nu_{R,s})$ is nonzero, $m(\mu_R)\geq b$. Splitting according to whether the discrepancy exceeds $\varepsilon$ gives</p>
<div class="math-display">$$\begin{aligned}
\eta_R^{-1}\big|\mathbb E f(\mu_R)-\mathbb E f(\nu_{R,s})\big|
&\leq\operatorname{Lip}(f)\varepsilon\eta_R^{-1}\mathbb P(m(\mu_R)\geq b)\\
&\quad+2\|f\|_\infty\eta_R^{-1}\mathbb P(m(\mu_R-\nu_{R,s})&gt;\varepsilon).
\end{aligned}$$</div>
<p>First send $R$ to infinity, then $s$ to infinity, and finally $\varepsilon$ to zero. The assumed cutoff limits identify the answer as $\mathcal N[f]$. The bounded-Lipschitz criterion, including $F=1$, gives weak convergence of the finite weighted measures.</p>
<p>For the restriction $m\geq a$, approximate its indicator on a bounded mass interval by Lipschitz cutoffs. The error near $a$ is bounded by a continuous majorant of a shrinking interval around $a$; the weighted convergence already proved and $\mathcal N(m=a)=0$ make this error vanish. The assumed uniform upper-tail estimate removes the upper truncation. Its limiting counterpart follows from finiteness of $\mathcal N$ on $\{m\geq a/2\}$. This proves weak convergence of the unnormalized restrictions. Their total masses converge to the positive number $\mathcal N(m\geq a)$; dividing gives the conditional law.</p>
<p>For embedded clusters, $\mu_R=z_R^{-1}\sum_{x\in K}\delta_{x/R}$ and $\nu_{R,s}=z_R^{-1}\sum_{x\in C_{R,s}}\delta_{x/R}$ have discrepancy $|K\setminus C_{R,s}|/z_R$. L9YJ supplies its bound. The same regularly varying tail gives both mass assumptions here, since $F(Bz_R)/F(z_R)\to B^{-\rho}$ for fixed $B$. Thus the remaining input is the cutoff double limit to the specified $\mathcal N$. A size-biased probability limit at a single cutoff scale, by itself, is not this input. These are the separate steps in <a href="https://arxiv.org/html/2508.18807v1">Critical LRP I</a>, §I.5.4 and Lemma I.5.33.</p>

## The measures obtained at a fixed cutoff ratio {#section-cutoff-ratio-laws}

<a id="tag-DX2Y" data-assertion="proposition" data-title="Undoing volume bias gives the fixed-ratio cutoff measures and their diagrams"></a>
<p>Use the scale functions in <a href="/tag/57FJ/">57FJ</a>. Let $K_r$ be random finite nonempty clusters with $\mathbb E|K_r|=\chi(r)$, and suppose that, for every fixed $s\geq1$, the measures</p>
<div class="math-display">$$V_{R,s}=\frac1{\widehat m(q(sR))}\sum_{x\in K_{q(sR)}}\delta_{x/(sR)}$$</div>
<p>under bias by $|K_{q(sR)}|/\chi(q(sR))$ converge in law to a common probability law $Q$ on $\mathcal M$. Assume $Y=m(V)$ under $Q$ has the squared-standard-normal law. Write $D_s$ for spatial dilation by $s$ and define $A_sV=4s^{2\beta}(D_s)_*V$. Define a measure $\Lambda_s$ on $\mathcal M\setminus\{0\}$ by</p>
<div class="math-display">$$\Lambda_s[F]=\frac{s^{-\beta}}4\mathbb E_Q\left[\frac{F(A_sV)}{m(V)}\right]\qquad(F\geq0).$$</div>
<p>For every nonnegative continuous $g$ compactly supported in $(0,\infty)$, the finite weighted laws of $\nu_{R,s}=\zeta(R)^{-1}\sum_{x\in K_{q(sR)}}\delta_{x/R}$ satisfy</p>
<div class="math-display">$$\eta(R)^{-1}\mathbb E[g(m(\nu_{R,s}))\mathbf1_{\{\nu_{R,s}\in\cdot\}}]\Longrightarrow g(m)\Lambda_s\qquad(R\to\infty).$$</div>
<p>There is a constant $C$ independent of $s\geq1$ and $b&gt;0$ such that $\Lambda_s(m\geq b)\leq Cb^{-1/2}$. If, in addition, $Q$ satisfies the inverse-mass diagram identity</p>
<div class="math-display">$$\mathbb E_Q\left[\frac1{m(V)}\prod_{i=1}^nV[\varphi_i]\right]=D_n(\varphi_1,\ldots,\varphi_n)$$</div>
<p>for all nonnegative compactly supported continuous $\varphi_i$, where $D_n$ is the $\kappa$-diagram of <a href="/tag/GFEM/">GFEM</a>, then</p>
<div class="math-display">$$\Lambda_s\left[\prod_{i=1}^n\mu[\varphi_i]\right]=4^{n-1}\sum_{T\in\mathbb T_n}\int\prod_{\{u,v\}\in E(T)}K_s(x_u-x_v)\prod_{i=1}^n\varphi_i(x_i)\prod_{v\ne0}dx_v,$$</div>
<p>with $K_s(x)=s^{\beta-d}\kappa(x/s)$. Under the kernel hypotheses of <a href="/tag/42PB/">42PB</a> and $d&gt;2\beta$, these moments converge to the corresponding Green-kernel diagrams.</p>
<p><em>Proof.</em> Put $a_{R,s}=4\widehat m(q(sR))/\widehat m(q(R))$. The exact change of measure gives, for bounded continuous $F$,</p>
<div class="math-display">$$\frac{\mathbb E[g(m(\nu_{R,s}))F(\nu_{R,s})]}{\eta(R)}
=\frac{\chi(q(sR))}{\eta(R)\widehat m(q(sR))}\,
\mathbb E_{\rm bias}\left[\frac{g(a_{R,s}m(V_{R,s}))F(a_{R,s}(D_s)_*V_{R,s})}{m(V_{R,s})}\right].$$</div>
<p>57FJ gives $a_{R,s}\to4s^{2\beta}$ and the prefactor tends to $s^{-\beta}/4$. Because $g$ vanishes near zero, the integrand extends continuously by zero at the zero measure and is bounded, uniformly for $a_{R,s}$ in a compact neighborhood of its positive limit. Weak convergence applies; the dependence on the convergent scalar is harmless by joint continuity and tightness. This proves the fixed-$s$ statement.</p>
<p>The density of $Y$ is $(2\pi y)^{-1/2}e^{-y/2}$ on $y&gt;0$. Therefore</p>
<div class="math-display">$$\Lambda_s(m\geq b)=\frac{s^{-\beta}}{4\sqrt{2\pi}}\int_{b/(4s^{2\beta})}^\infty y^{-3/2}e^{-y/2}\,dy\leq\frac{1}{\sqrt{2\pi b}}.$$</div>
<p>For the moment formula, the inverse-mass identity gives $4^{n-1}s^{(2n-1)\beta}D_n(\varphi_1(s\cdot),\ldots,\varphi_n(s\cdot))$. Change all $2n-1$ integration variables from $x_v$ to $sx_v$. A binary tree here also has $2n-1$ edges, so distributing the spatial Jacobian and the prefactor over the edges gives exactly the displayed $K_s$ integral. Its limit follows from 42PB.</p>
<p>The inverse-mass identity is an explicit input. It follows from the cutoff polynomial diagram asymptotics, not just from the total-mass law: the finite moment-measure argument in Y3SX first extends those asymptotics to bounded continuous spatial tests. After biasing, the relevant observable is $m(V)^{-1}\prod_iV[\varphi_i]$. It is continuous off the zero measure and bounded in absolute value by a constant times $m(V)^{n-1}$. Higher total-mass moments give uniform integrability, and the squared-normal limit has no atom at zero, so the identity passes to $Q$. Alternatively, 45EB supplies it from the stated CRT input and spatial construction. This identifies exactly which spatial information is used when undoing bias.</p>

## Identifying a measure from local mass moments {#section-local-moment-identification}

<a id="tag-W9BP" data-assertion="theorem" data-title="Local mixed moments and spatial tightness determine the canonical weighted limit"></a>
<p>Let $\Lambda_j$ and $\mathcal N$ be positive Borel measures on $\mathcal M\setminus\{0\}$, each finite on $\{m\geq b\}$ for every $b&gt;0$. Suppose $\sup_j\Lambda_j(m\geq b)&lt;\infty$ for every $b&gt;0$, and</p>
<div class="math-display">$$\lim_{B\to\infty}\sup_j\Lambda_j(m\geq B)=0,\qquad
\lim_{L\to\infty}\sup_j\Lambda_j\bigl(\mu(\{|x|&gt;L\})&gt;\varepsilon\bigr)=0\quad(\varepsilon&gt;0).$$</div>
<p>Assume convergence of all local mixed moments of positive degree: for $n\geq1$ and nonnegative compactly supported continuous $\varphi_1,\ldots,\varphi_n$,</p>
<div class="math-display">$$\Lambda_j\left[\prod_{i=1}^n\mu[\varphi_i]\right]\longrightarrow\mathcal N\left[\prod_{i=1}^n\mu[\varphi_i]\right]&lt;\infty.$$</div>
<p>Finally, suppose $\mathcal N[\mu[\varphi]^n]\leq C_\varphi^n n!$ for every such $\varphi$ and $n\geq1$. Then, for every nonnegative Lipschitz $g$ compactly supported in $(0,\infty)$,</p>
<div class="math-display">$$g(m)\Lambda_j\Longrightarrow g(m)\mathcal N$$</div>
<p>as finite measures on $\mathcal M$.</p>
<p><em>Proof.</em> Fix a nonnegative $\psi\in C_c(\mathbb R^d)$. First weight the measures by the local mass $\mu[\psi]$. Their total masses converge by the degree-one hypothesis. If the limiting total is zero, their weak convergence to zero follows immediately. Otherwise normalize them to probability laws.</p>
<p>These laws are tight on $\mathcal M$. Indeed, for any Borel event $E$, Cauchy–Schwarz gives</p>
<div class="math-display">$$\Lambda_j[\mu[\psi]\mathbf1_E]\leq\Lambda_j[\mu[\psi]^2]^{1/2}\Lambda_j(E)^{1/2}.$$</div>
<p>The first factor is uniformly bounded. Apply the two uniform tail assumptions to the events of excessive total mass and excessive mass outside a large ball. Choose a sequence of balls with summable error probabilities and successively smaller allowed outside masses. Except on an arbitrarily small event, the random measure belongs to a uniformly bounded, uniformly tight collection of finite measures, whose closure is compact. This proves tightness of the weighted laws.</p>
<p>Every subsequential limit has the mixed moments of $\mu[\psi]\mathcal N$, by the moment hypothesis with one additional factor $\mu[\psi]$. Higher local moments give the uniform integrability needed here: a fixed product of local integrals is dominated by a power of $\mu[\psi+\sum_i\varphi_i]$. These moments determine the weighted law. To see this, use $h=\psi+\sum_i\varphi_i$; its factorial bound implies</p>
<div class="math-display">$$\mathcal N[\mu[\psi](\mu[h])^k]\leq\mathcal N[\mu[h]^{k+1}]\leq C_h^{k+1}(k+1)!.$$</div>
<p>Summing the exponential series gives a moment generating function near zero for each finite vector of nonnegative local integrals under the normalized weighted law. Its joint moments therefore determine its distribution. A countable collection of compactly supported continuous tests separates finite measures and generates their Borel sigma field; total mass is the increasing limit of such local integrals. Thus the weighted law is unique, and $\mu[\psi]\Lambda_j\Rightarrow\mu[\psi]\mathcal N$.</p>
<p>The function $u\mapsto g(u)/u$, extended by zero at zero, is bounded and continuous. Testing the last convergence with $F(\mu)g(\mu[\psi])/\mu[\psi]$ for bounded continuous $F$ gives $g(\mu[\psi])\Lambda_j\Rightarrow g(\mu[\psi])\mathcal N$.</p>
<p>Choose $0\leq\psi_L\leq1$ compactly supported and equal to one on $B_L$, increasing to one. Then $0\leq m-\mu[\psi_L]\leq\mu(B_L^c)$. If $g$ vanishes below $b&gt;0$, the error in replacing $g(m)$ by $g(\mu[\psi_L])$, integrated against a bounded $F$, is at most</p>
<div class="math-display">$$\|F\|_\infty\left(\operatorname{Lip}(g)\varepsilon\Lambda_j(m\geq b)+2\|g\|_\infty\Lambda_j(\mu(B_L^c)&gt;\varepsilon)\right).$$</div>
<p>Let $L$ increase, then $\varepsilon$ decrease. The error vanishes uniformly in $j$. The same replacement is valid for $\mathcal N$: the events $\mu(B_L^c)&gt;\varepsilon$ decrease to the empty set and lie inside the finite-measure set $\{m&gt;\varepsilon\}$. Combining with the local weighted convergence proves the theorem.</p>
<p>Apply this theorem to the measures $\Lambda_s$ in DX2Y. The Green-diagram convergence of 42PB supplies their local mixed-moment limits, and 5VYE supplies the factorial bound for the canonical measure. DX2Y gives the uniform total-mass tails. The spatial tails follow from ALO4 in the cluster application: first truncate total mass to a compact interval away from zero, pass the fixed-$s$ limits by the portmanteau theorem, and then remove the upper truncation using the common tail bound. Domination of every cutoff cluster by the full cluster makes the resulting estimate uniform in $s$.</p>
<p>This establishes the cutoff double limit needed in BB3O from explicit diagram and tightness inputs. BB3O then removes the cutoff and, at thresholds with no canonical mass atom, gives the large-volume conditional limit. The reconstruction covers the analytic and measure-theoretic passage in Critical LRP I §I.5.4. Its percolation inputs remain the cutoff mixed-moment asymptotics, full volume tail, omitted-edge row estimate, and fixed-cutoff second spatial moments; existence and the moment formula of the intended canonical superprocess measure are also inputs. No unproved model-specific estimate is replaced by a conclusion about its scalar moments.</p>

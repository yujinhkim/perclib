---
{
  "id": "cutoff-hydrodynamics",
  "title": "Cutoff hydrodynamics and moment growth",
  "subtitle": "The direct-merge scale and a low-dimensional contradiction",
  "kind": "method",
  "category": "Critical phenomena",
  "summary": "Rooted exponential damping compares finite-window moments. Explicit moment equations then rule out a largest-cluster scale smaller than the direct-merge scale below the upper critical dimension.",
  "context": ["Clusters form a common random partition; observation windows are finite and nonempty.", "The cutoff law and the observation window have separate scale parameters.", "Differential equations and their probabilistic error bounds are hypotheses where stated."],
  "related": ["cutoff-localization", "finite-set-hyperscaling", "spatial-cutoff-moments", "marginal-ode", "universal-tightness"],
  "sourceIds": ["notes", "hutchcroft-lrp-2"],
  "aliases": ["hydrodynamic condition", "direct-merge scale", "bad interval", "low-dimensional hyperscaling", "rooted damping"],
  "prototypeUses": []
}
---

## The direct-merge scale {#section-scale}

<p>Under the cutoff law at radius $r$, let $Z_{r,R}=\max_x|K_x\cap B_R|$ and</p>
<div class="math-display">$$M(r,R)=\min\{n\geq1:\mathbb P_r(Z_{r,R}\geq n)\leq e^{-1}\},\qquad M_r=M(r,r).$$</div>
<p>The maximum can be taken over roots in $B_R$: every cluster meeting the window contains such a root. Paths may leave the window. In particular, $2\leq M(r,R)\leq|B_R|+1$. The quantity $M(r,Cr)$ retains cutoff $r$ while enlarging the observation window; $M_{Cr}=M(Cr,Cr)$ changes both. Their comparison requires a coupling of the cutoff laws.</p>

<a id="tag-UWLQ" data-assertion="definition" data-title="Hydrodynamic condition at the direct-merge scale"></a>
<p>For parameters $d,\alpha&gt;0$, put $h=(d+\alpha)/2$. The cutoff family satisfies the hydrodynamic condition if $M_r/r^h\to0$ as $r\to\infty$.</p>

<a id="tag-UUQO" data-assertion="proposition" data-title="Independent cross edges identify the direct-merge scale"></a>
<p>Let $A,B$ be disjoint finite vertex sets. Independently for each $u\in A,v\in B$, open the edge $\{u,v\}$ with probability $1-e^{-\beta J(u,v)}$, where $\beta&gt;0$. Suppose, for fixed positive $c_-,c_+$ and $r&gt;0$,</p>
<div class="math-display">$$c_-r^{-d-\alpha}\leq J(u,v)\leq c_+r^{-d-\alpha}.$$</div>
<p>Then the probability $P_{A,B}$ of at least one direct edge satisfies</p>
<div class="math-display">$$1-e^{-\beta c_-r^{-d-\alpha}|A||B|}\leq P_{A,B}\leq1-e^{-\beta c_+r^{-d-\alpha}|A||B|}.$$</div>
<p>In particular, if both cardinalities are between $ar^h$ and $br^h$, for fixed $0&lt;a\leq b&lt;\infty$, the direct-edge probability stays bounded away from zero and one. If $|A||B|=o(r^{d+\alpha})$, it tends to zero.</p>
<p><em>Proof.</em> Distinct pairs between the disjoint sets give distinct edge coordinates. Their closed probabilities multiply, so $P_{A,B}=1-\exp(-\beta\sum_{u\in A,v\in B}J(u,v))$. Bound the sum and use $2h=d+\alpha$.</p>
<p>The same calculation holds conditionally when, given the information determining $A,B$, their cross edges still have the stated independent laws. For example, this applies to sets selected using only the internal edges of two fixed disjoint domains. It cannot be applied without further justification to clusters revealed by exploring the cross edges themselves. For a Euclidean power-law kernel, the displayed two-sided intensity bounds follow when all the cross distances are comparable to $r$.</p>

## Two finite-window moment estimates {#section-moments}

<a id="tag-BZDZ" data-assertion="proposition" data-title="Rooted exponential damping controls higher moments"></a>
<p>Let $X\geq0$ be a random variable, $M,A,b&gt;0$, and suppose</p>
<div class="math-display">$$\mathbb P(X\geq tM)\leq A e^{-bt}\mathbb P(X\geq M)\qquad(t\geq1).$$</div>
<p>For any $p,q&gt;0$ with $\mathbb E X^p&lt;\infty$,</p>
<div class="math-display">$$\mathbb E X^{p+q}\leq D_{p,q}M^q\mathbb E X^p,\qquad D_{p,q}=1+Ae^{-b}+A(p+q)\int_1^\infty t^{p+q-1}e^{-bt}\,dt&lt;\infty.$$</div>
<p><em>Proof.</em> On $\{X\leq M\}$, use $X^{p+q}\leq M^qX^p$. On its complement the layer-cake identity gives</p>
<div class="math-display">$$\mathbb E[X^{p+q}\mathbf1_{\{X&gt;M\}}]=M^{p+q}\mathbb P(X&gt;M)+(p+q)\int_M^\infty t^{p+q-1}\mathbb P(X&gt;t)\,dt.$$</div>
<p>Apply the tail hypothesis, substitute $t=Ms$, and use $M^p\mathbb P(X\geq M)\leq\mathbb E X^p$. This proves both the inequality and finiteness of the higher moment.</p>
<p>For the rooted tightness bound in the notes, $A=e$ and $b=1/9$. With $X=|K_o\cap B_R|$ under cutoff $r$, the appropriate quantile is $M(r,R)$. If the laws admit an increasing coupling as the cutoff grows, then $M(r,Cr)\leq M(Cr,Cr)=M_{Cr}$ for $C\geq1$; this follows by comparing every tail probability before taking the integer quantile.</p>

<a id="tag-LQ6Y" data-assertion="proposition" data-title="Largest-intersection quantiles give lower rooted moments"></a>
<p>Let $\Lambda$ be a finite nonempty set in a common random partition. Put $Z=\max_x|K_x\cap\Lambda|$ and $M=\min\{n\geq1:\mathbb P(Z\geq n)\leq e^{-1}\}$. For every $p&gt;0$,</p>
<div class="math-display">$$\sum_{x\in\Lambda}\mathbb E|K_x\cap\Lambda|^p\geq\mathbb E Z^{p+1}\geq\frac{M^{p+1}}{e\,2^{p+1}}.$$</div>
<p>If the full-cluster $p$th moments are the same at every root and equal $m_p$, then $m_p\geq M^{p+1}/(e\,2^{p+1}|\Lambda|)$, allowing extended moments.</p>
<p><em>Proof.</em> The nonempty cluster intersections partition $\Lambda$. If their sizes are $s_i$, counting each root in its own intersection gives $\sum_{x\in\Lambda}|K_x\cap\Lambda|^p=\sum_i s_i^{p+1}\geq Z^{p+1}$. Quantile minimality gives $M\geq2$ and $\mathbb P(Z\geq M-1)&gt;e^{-1}$; also $M-1\geq M/2$. Take expectations. For the last conclusion, bound each intersection by its full cluster.</p>

## Failure of hydrodynamics from explicit moment equations {#section-contradiction}

<a id="tag-XB1X" data-assertion="theorem" data-title="Moment equations contradict a sub-merge largest-cluster scale below three alpha"></a>
<p>Fix $d,\alpha&gt;0$ with $d&lt;3\alpha$, and put $h=(d+\alpha)/2$. Let $m_1,m_2$ be positive locally absolutely continuous functions on $[r_0,\infty)$, and let $M$ be a positive function there. Suppose $m_1(r)\asymp r^\alpha$. Suppose there are constants $a_0,K&gt;0$, $C\geq1$, and measurable functions $a&gt;0$, $e_1,e_2\in[0,1]$ such that $a(r)\sim a_0r^{-\alpha-1}$ and, almost everywhere,</p>
<div class="math-display">$$m_1'=a m_1^2(1-e_1),\qquad m_2'=3a m_1m_2(1-e_2).$$</div>
<p>Assume also, for all sufficiently large $r$,</p>
<div class="math-display">$$e_i(r)\leq K\frac{M(Cr)^2}{r^{d+\alpha}}\quad(i=1,2),\qquad m_2(r)\leq K M(Cr)m_1(r).$$</div>
<p>Then $M(r)/r^h$ does not tend to zero. Equivalently, it is bounded below by a positive constant along an unbounded sequence of radii.</p>
<p><em>Proof.</em> Suppose $M(r)=o(r^h)$. Since $C$ is fixed, both errors tend to zero. The first equation and $m_1(r)\to\infty$ give</p>
<div class="math-display">$$\frac1{m_1(r)}=\int_r^\infty a(s)(1-e_1(s))\,ds\sim\frac{a_0}{\alpha}r^{-\alpha}.$$</div>
<p>Indeed, integrate the derivative of $-1/m_1$ on a finite interval and then send its upper endpoint to infinity; the integrand is asymptotic to the displayed integrable power. It follows that $m_1(r)\sim(\alpha/a_0)r^\alpha$. The second equation now gives $(\log m_2)'=(3\alpha+o(1))/r$ almost everywhere. Integrating between $r$ and $tr$ for each fixed $t&gt;0$ shows $m_2(tr)/m_2(r)\to t^{3\alpha}$; integrating from a fixed radius also gives $m_2(r)=r^{3\alpha+o(1)}$.</p>
<p>On the other hand, the assumed upper bound and hydrodynamics give $m_2(r)=o(r^{h+\alpha})$. This is impossible because $h+\alpha=(d+3\alpha)/2&lt;3\alpha$.</p>
<p>This argument uses a fixed $C$, not a scale factor tending to infinity with $r$. In applications, weak cutoff localization with a fixed error, such as $\varepsilon=1$, can suffice for constant-factor moment bounds. It must still be combined with rooted damping, monotone cutoff coupling and the model's differential error estimates. The theorem does not derive those estimates from (wCL) alone.</p>

## The interval estimate behind a stronger lower bound {#section-interval}

<a id="tag-DISO" data-assertion="proposition" data-title="A moment growing faster than its upper envelope cannot remain on a long interval"></a>
<p>Let $C\geq1$, $s&gt;0$, $R\geq Cs$, $B\geq b&gt;0$, and $\lambda&gt;k$. Let $f$ be positive and locally absolutely continuous on $[s,R/C]$. If</p>
<div class="math-display">$$f(s)\geq bs^k,\qquad f(R/C)\leq B(R/C)^k,\qquad (\log f)'(t)\geq\frac\lambda t\ \text{a.e.},$$</div>
<p>then $R/s\leq C(B/b)^{1/(\lambda-k)}$.</p>
<p><em>Proof.</em> Integration gives $f(R/C)\geq bs^k(R/(Cs))^\lambda$. Compare with the upper bound and divide by $b(R/C)^k$.</p>
<p>In the notes' application, $k=\alpha+h$. At a scale with $M_s\geq\delta s^h$, the preceding quantile bound and $|B_s|\preceq s^d$ give $m_2(s)\succeq s^{3h-d}=s^k$. If a derivative lower bound with exponent $\lambda&gt;k$ holds throughout a subsequent interval of small quantiles, and $m_2(t)\preceq t^k$ holds at its far endpoint, the proposition bounds the interval's multiplicative length. These endpoint and derivative hypotheses are essential. Turning the subsequence conclusion into a lower bound at every large scale additionally requires controlling the intervals between good scales and monotonicity of the cutoff-window quantile. No such upgrade is inferred merely from the contradiction theorem.</p>

## Extending the lower bound to every large scale {#section-all-scales}

<a id="tag-YEVN" data-assertion="theorem" data-title="A last-good-scale argument gives a uniform quantile lower bound"></a>
<p>Let $d,h,r_0,c,B,\delta&gt;0$, $C\geq1$, and put $k=3h-d$. Let $M:[r_0,\infty)\to(0,\infty)$ be nondecreasing and let $f$ be positive and locally absolutely continuous. Suppose for every $r\geq r_0$,</p>
<div class="math-display">$$c\frac{M(r)^3}{r^d}\leq f(r)\leq Br^k.$$</div>
<p>Suppose also that for some $\lambda&gt;k$, almost every $r\geq r_0$ satisfies</p>
<div class="math-display">$$M(Cr)\leq\delta(Cr)^h\quad\Longrightarrow\quad(\log f)'(r)\geq\frac\lambda r.$$</div>
<p>If $M(r_*)\geq\delta r_*^h$ for some $r_*\geq r_0$, then, with</p>
<div class="math-display">$$L=C\left(\frac{B}{c\delta^3}\right)^{1/(\lambda-k)},$$</div>
<p>one has $L\geq C$ and $M(R)\geq\delta L^{-h}R^h$ for every $R\geq r_*$.</p>
<p><em>Proof.</em> The two bounds on $f(r_*)$ imply $B\geq c\delta^3$, so $L\geq C$. Fix $R\geq r_*$. Let $s$ be the supremum of the good scales in $[r_*,R]$, where a scale $u$ is good if $M(u)\geq\delta u^h$. Then $s$ is itself good. Indeed, either it is attained or there is a sequence of good scales increasing to it, and monotonicity gives $M(s)\geq\delta s^h$ by taking the limit. No continuity of the quantile function is required.</p>
<p>Every $u\in(s,R]$ is bad. If $R&lt;Cs$, then $R/s&lt;C\leq L$. Otherwise, for almost every $t\in(s,R/C)$ the scale $Ct$ is bad, so $(\log f)'(t)\geq\lambda/t$. Also $f(s)\geq c\delta^3s^k$ and $f(R/C)\leq B(R/C)^k$. The preceding interval estimate therefore gives $R/s\leq L$. In both cases, monotonicity yields $M(R)\geq M(s)\geq\delta s^h\geq\delta L^{-h}R^h$.</p>

<a id="tag-NS0Q" data-assertion="corollary" data-title="Conditional all-scale largest-cluster order from cutoff moment equations"></a>
<p>Under the hypotheses of <a href="/tag/XB1X/">the hydrodynamic contradiction theorem</a>, suppose additionally that $M$ is nondecreasing and, for some $c,U&gt;0$ and all sufficiently large $r$,</p>
<div class="math-display">$$m_2(r)\geq c\frac{M(r)^3}{r^d},\qquad M(r)\leq Ur^h,\qquad h=\frac{d+\alpha}{2}.$$</div>
<p>Then $M(r)\asymp r^h$ as $r\to\infty$.</p>
<p><em>Proof.</em> Put $k=\alpha+h=3h-d$. The assumed bound $m_2(r)\leq K M(Cr)m_1(r)$ and $m_1(r)\asymp r^\alpha$ give $m_2(r)\leq Br^k$ for some finite $B$. The first moment equation, $e_1\geq0$, and $m_1(r)\to\infty$ give</p>
<div class="math-display">$$\frac1{m_1(r)}=\int_r^\infty a(t)(1-e_1(t))\,dt\leq\int_r^\infty a(t)\,dt\sim\frac{a_0}{\alpha}r^{-\alpha}.$$</div>
<p>Consequently $\liminf_{r\to\infty}r a(r)m_1(r)\geq\alpha$. Choose $\eta\in(0,1)$ so small that $\lambda=3\alpha(1-\eta)^2&gt;k$, which is possible because $d&lt;3\alpha$. Beyond a fixed scale, $a(r)m_1(r)\geq\alpha(1-\eta)/r$. Choose $\delta&gt;0$ sufficiently small that $K\delta^2C^{2h}\leq\eta$. If $M(Cr)\leq\delta(Cr)^h$, the second error is at most $\eta$, and hence</p>
<div class="math-display">$$(\log m_2)'(r)=3a(r)m_1(r)(1-e_2(r))\geq\frac\lambda r\quad\text{a.e.}$$</div>
<p>The contradiction theorem gives $\limsup M(r)/r^h&gt;0$. Decrease $\delta$ if necessary to obtain a good scale beyond every fixed lower threshold. The last-good-scale theorem, applied to $f=m_2$, now supplies a uniform lower bound. The upper bound is an assumption.</p>
<p>For a transitive cutoff law and finite windows with $|B_r|\leq V_0r^d$, the <a href="/tag/LQ6Y/">quantile moment estimate</a> gives both additional moment comparisons: its $p=1$ case and $m_1(r)\preceq r^\alpha$ give $M_r\preceq r^h$, while its $p=2$ case gives $m_2(r)\geq M_r^3/(8eV_0r^d)$. An increasing coupling of the cutoff laws, together with increasing windows, makes $M_r$ nondecreasing. Thus these geometric inputs can be verified separately; the differential equations and their error bounds remain substantive hypotheses.</p>
<p>The analytic hypotheses are consistent. For any $d,\alpha&gt;0$ with $d&lt;3\alpha$, take $M(r)=r^h$, $m_1(r)=r^\alpha$, $m_2(r)=r^k$, $a(r)=\alpha r^{-\alpha-1}$, $e_1=0$ and $e_2=1-k/(3\alpha)$. They satisfy the hypotheses with $C=K=c=U=1$. This is a witness for the scalar equations, not a claim that these exact functions are moments of a percolation model.</p>

## Source scope {#section-source}

<p>The hydrodynamic definition is S042 (lines 5786–5791). The proof components above cover the analytic contradiction and finite-box estimates surrounding S043 (lines 5803–6050). The two-cluster differential identities and their error bounds remain model-specific inputs; neither the complete low-dimensional theorem S041 nor its full critical volume-tail asymptotic is asserted here. The source's marginal logarithms also require separate estimates, beyond the definition of hydrodynamics.</p>

<p>The proposed full-model tail in S041 is $n^{-(d-\alpha)/(d+\alpha)}$. As a two-sided estimate for an almost surely finite cluster, it requires $\alpha&lt;d$: if $\alpha&gt;d$ the lower bound eventually exceeds one, while if $\alpha=d$ it is bounded away from zero. Thus the decaying-tail interpretation below $3\alpha$ concerns $\alpha&lt;d&lt;3\alpha$, together with the additional localization hypotheses. This restriction is not supplied merely by $d&lt;3\alpha$.</p>

<p>The paper’s introduction to §II.1.2 explicitly includes $\alpha=d$ as a possible discontinuous endpoint under its localization hypothesis. That case is outside the finite-cluster, decaying-tail interpretation above; it is not ruled out by a fractional-tail argument.</p>

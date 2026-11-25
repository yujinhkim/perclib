---
{
  "id": "backbone-connections",
  "title": "Backbone counts from disjoint connections",
  "subtitle": "Counting identities, moment bounds and the cutoff reduction",
  "kind": "method",
  "category": "Methods",
  "summary": "The disjoint-connection backbone observable has an exact invariant counting identity, a BK upper bound, and a two-ghost small-field representation. Cluster exploration gives a reverse bound with a triangle error and a high-dimensional multiple-arm consequence; the bubble-only bound remains open.",
  "context": ["Independent bonds on a countable group with a left-invariant law for the counting identity.", "Disjointness means edge-disjoint open witnesses; empty paths are allowed.", "The two ghost fields use independent marks, including at the same vertex."],
  "related": ["disjoint-occurrence", "ghost-fields", "connection-kernels", "intrinsic-geometry", "susceptibility"],
  "sourceIds": ["notes", "hutchcroft-lrp-3"],
  "aliases": ["backbone", "two ghosts", "reverse BK", "disjoint connections", "bubble condition"],
  "prototypeUses": []
}
---

## Which backbone is being counted {#section-definition}

<a id="tag-EJHT" data-assertion="definition" data-title="Disjoint-connection backbone count"></a>
<p>For vertices $u,v,z$ in a countable graph, let $D(u,z;z,v)$ be the event that an open path from $u$ to $z$ and an open path from $z$ to $v$ have disjoint edge sets. Paths of length zero have empty edge sets. Define the extended nonnegative count</p>
<div class="math-display">$$B_\omega(u,v)=\sum_z\mathbf1_{D(u,z;z,v)}.$$</div>
<p>Equivalently, the event in the summand is the disjoint occurrence $\{u\leftrightarrow z\}\circ\{z\leftrightarrow v\}$. It implies $u\leftrightarrow v$. The count is increasing under edge addition.</p>
<p>This observable is neither chemical distance nor the number of pivotal edges. It need not count only vertices on simple paths from $u$ to $v$: take a triangle with vertices $u,a,z$ and attach a single edge from $u$ to $v$. When all four edges are open, the paths $u-a-z$ and $z-u-v$ have disjoint edge sets, so $z$ is counted. But every simple path from $u$ to $v$ is the single attached edge. The definition permits the two paths to share vertices other than their common endpoint; it requires only edge-disjointness.</p>

## Recentring the count {#section-counting}

<a id="tag-RIRJ" data-assertion="theorem" data-title="Invariant backbone counting identity and BK bounds"></a>
<p>Let the vertex set be a countable group with identity $o$, and let the independent-bond law be invariant under left multiplication. Put $\chi=\mathbb E|K_o|$. Then, as nonnegative extended quantities,</p>
<div class="math-display">$$\mathbb E\sum_{x\in K_o}B_\omega(o,x)=\sum_{u,v}\mathbb P\bigl(\{o\leftrightarrow u\}\circ\{o\leftrightarrow v\}\bigr),\qquad \chi\leq\mathbb E\sum_{x\in K_o}B_\omega(o,x)\leq\chi^2.$$</div>
<p><em>Proof.</em> The summand defining $B_\omega(o,x)$ vanishes unless $x\in K_o$, so Tonelli allows us to sum over all $x,z$. Translate by $z^{-1}$. The two connections become $z^{-1}\leftrightarrow o$ and $o\leftrightarrow z^{-1}x$, with their disjoint witnesses preserved. The map $(z,x)\mapsto(u,v)=(z^{-1},z^{-1}x)$ is a bijection of the group squared. Invariance and reindexing give the identity.</p>
<p>BK bounds each summand on the right by $\tau(o,u)\tau(o,v)$, giving the upper bound. For countably many bonds this use of BK follows from finite-coordinate BK: restrict witnesses to increasing finite edge sets; every pair of finite disjoint open paths eventually appears, so the disjoint events and the connection events converge upwards. The lower bound follows by taking only the summands $u=o$, where the first connection has an empty witness.</p>
<p>All sums are nonnegative, so the argument requires no finite susceptibility. Finiteness is needed if one wants the inequalities to compare finite scales. The group hypothesis is used for the explicit change of variables; a general transitive graph requires an appropriate mass-transport assumption instead.</p>

## A lower bound from the second cluster moment {#section-moment-lower}

<a id="tag-44CZ" data-assertion="proposition" data-title="The backbone expectation dominates the second moment divided by susceptibility"></a>
<p>In the invariant independent-bond model of <a href="/tag/RIRJ/">RIRJ</a>, suppose $\chi=\mathbb E|K_o|&lt;\infty$. Write</p>
<div class="math-display">$$S=\mathbb E\sum_xB_\omega(o,x),\qquad m_2=\mathbb E|K_o|^2.$$</div>
<p>Then $m_2$ is finite and</p>
<div class="math-display">$$\frac{m_2}{\chi}\leq S\leq\chi^2.$$</div>
<p><em>Proof.</em> If $o,u,v$ are connected, prune a finite open tree joining them. Its median $z$ has three edge-disjoint arms to the marked vertices, with empty arms allowed. Thus</p>
<div class="math-display">$$\{o,u,v\text{ connected}\}\subseteq
\bigcup_z\left(\{o\leftrightarrow z\}\circ
\bigl(\{z\leftrightarrow u\}\circ\{z\leftrightarrow v\}\bigr)\right).$$</div>
<p>Apply BK between the first arm event and the parenthesized event, keeping the latter intact. Summing over $u,v,z$ and using invariance gives</p>
<div class="math-display">$$m_2\leq\sum_z\tau(o,z)\sum_{u,v}\mathbb P\bigl(\{z\leftrightarrow u\}\circ\{z\leftrightarrow v\}\bigr)=\chi S.$$</div>
<p>For countably many bonds, restrict the finite path witnesses to finite edge sets before applying BK and take increasing limits. Tonelli justifies the sums, even before finiteness is known. RIRJ gives $S\leq\chi^2$, so $m_2\leq\chi^3&lt;\infty$. Since $\chi\geq1$, division proves the lower bound.</p>
<p>This is the moment bound in <a href="https://github.com/tomhutchcroft/lrp/issues/242#issuecomment-6902840243">FIXER's critical-dimensional reduction</a>. In particular, the inputs $\chi_r\asymp r^\alpha$ and $m_{2,r}\asymp r^{3\alpha}(\log r)^{-1/2}$ imply only</p>
<div class="math-display">$$\frac{r^{2\alpha}}{\sqrt{\log r}}\lesssim S_r\lesssim r^{2\alpha}.$$</div>
<p>The moment inputs for the soft-cutoff model with $d=3\alpha&lt;6$ are recorded in <a href="https://arxiv.org/html/2508.18809v1#S1.SS3">Critical long-range percolation III, equations (III.1.16) and (III.1.18)</a>. They are cited inputs here. The lower bound does not establish $S_r\asymp\chi_r^2$.</p>

## Two independent ghost fields {#section-ghost-limit}

<a id="tag-32MY" data-assertion="theorem" data-title="Two-ghost limit for the disjoint-connection count"></a>
<p>On any countable graph with any random bond configuration, independently mark every vertex green in each of two independent fields, with probability $q_h=1-e^{-h}$ for $h&gt;0$. Let $D_h$ be the probability that there are vertices $u,v$, green in the first and second fields respectively, and edge-disjoint open paths from $o$ to $u$ and from $o$ to $v$. Then</p>
<div class="math-display">$$\lim_{h\downarrow0}\frac{D_h}{h^2}=\sum_{u,v}\mathbb P\bigl(\{o\leftrightarrow u\}\circ\{o\leftrightarrow v\}\bigr),$$</div>
<p>allowing the value infinity. The two vertices may coincide: their marks are distinct independent coordinates, even at the root.</p>
<p>In the invariant independent-bond model of the preceding theorem, suppose $\chi&lt;\infty$, and let $M(h)=\mathbb E[1-e^{-h|K_o|}]$ be the single-field connection probability. If $D_h\geq cM(h)^2$ for all sufficiently small $h&gt;0$, with fixed $c&gt;0$, then</p>
<div class="math-display">$$c\chi^2\leq\mathbb E\sum_{x\in K_o}B_\omega(o,x)\leq\chi^2.$$</div>
<p><em>Proof.</em> Denote the sum in the first display by $S$. For a fixed ordered pair $(u,v)$, the relevant bond event and its two green marks have probability $q_h^2\mathbb P(\{o\leftrightarrow u\}\circ\{o\leftrightarrow v\})$. A countable union bound gives $D_h\leq q_h^2S$.</p>
<p>For the reverse limit, restrict both endpoints to a finite set $F$. There are $|F|^2$ candidate pairs. Two distinct pairs require at least three distinct mark coordinates, since the two fields are distinguished; their joint probability is therefore at most $q_h^3$, regardless of the bond events. The first two terms of inclusion-exclusion give</p>
<div class="math-display">$$D_h\geq q_h^2\sum_{u,v\in F}\mathbb P\bigl(\{o\leftrightarrow u\}\circ\{o\leftrightarrow v\}\bigr)-\binom{|F|^2}{2}q_h^3.$$</div>
<p>Divide by $h^2$, use $q_h/h\to1$, and let $h\downarrow0$. Exhausting the vertex set by finite $F$ gives $\liminf D_h/h^2\geq S$. If $S&lt;\infty$, the union bound gives the matching upper limit; if $S=\infty$, the lower limit already proves the extended-valued assertion.</p>
<p>Finally, $M(h)/h\to\chi$ by the <a href="/tag/8B62/">single-field first-moment limit</a>. Divide the assumed reverse bound by $h^2$, take the limit, and use the counting identity and BK bound.</p>
<p>Here the ghost disjoint event includes distinct mark coordinates as part of its witnesses, while requiring disjointness of the bond paths. Treating the two fields as one would change the small-field order: a single green mark at the root would have probability of order $h$, rather than $h^2$.</p>

## Transferring a separated-root estimate {#section-transfer}

<a id="tag-I6SP" data-assertion="proposition" data-title="Finite-path transfer and a bounded-susceptibility two-ghost bound"></a>
<p>In the invariant independent-bond model, let $D_h(x,y)$ be the probability of edge-disjoint open paths from $x$ to the first ghost field and from $y$ to the second. Thus $D_h=D_h(o,o)$. Let $\gamma=(v_0=x,\ldots,v_\ell=y)$ be a fixed simple path with positive edge probabilities, and put $\rho_\gamma=\prod_{e\in\gamma}q_e$. Then, for every $h&gt;0$,</p>
<div class="math-display">$$D_h\geq\frac{\rho_\gamma}{\ell+1}D_h(x,y).$$</div>
<p>Independently of this path estimate, if $\chi=\mathbb E|K_o|&lt;\infty$, then</p>
<div class="math-display">$$D_h\geq(1-e^{-h})^2\geq\frac{M(h)^2}{\chi^2}.$$</div>
<p><em>Proof.</em> First consider a configuration in which every edge of $\gamma$ is open and $D_h(x,y)$ has witnesses $P_1,P_2$, ending at a mark of their respective fields. Traverse $\gamma$ from $x$ and let $v_j$ be its first vertex on $P_2$. Among $v_0,\ldots,v_j$, let $v_i$ be the last vertex on $P_1$. Both indices exist, because $x\in P_1$ and $y\in P_2$.</p>
<p>If $i=j$, the suffixes of $P_1$ and $P_2$ from that vertex give two disjoint ghost connections. If $i&lt;j$, the interior of the segment $v_i,\ldots,v_j$ meets neither witness. The suffix of $P_1$ from $v_i$ is therefore edge-disjoint from the path consisting of this segment followed by the suffix of $P_2$ from $v_j$. In either case, $D_h(v_i,v_i)$ occurs. Empty suffixes cause no problem: the two mark fields have distinct coordinates even at the same vertex.</p>
<p>Consequently the intersection of the all-open path event with the separated-root event is contained in $\bigcup_{i=0}^{\ell}D_h(v_i,v_i)$. Both events in the intersection are increasing in the independent bond and mark coordinates. Harris, the union bound and translation invariance give</p>
<div class="math-display">$$\rho_\gamma D_h(x,y)\leq\mathbb P(\gamma\text{ open},D_h(x,y))\leq\sum_{i=0}^{\ell}D_h(v_i,v_i)=(\ell+1)D_h.$$</div>
<p>For countably many coordinates, the use of Harris follows by restricting the finite path witnesses to finite sets and taking increasing limits. Finally, marking the root in both independent fields already gives $D_h\geq(1-e^{-h})^2$. Conditional on a finite cluster of size $t$, the union bound gives $1-e^{-ht}\leq t(1-e^{-h})$. Integration yields $M(h)\leq\chi(1-e^{-h})$ when $\chi&lt;\infty$, proving the second bound.</p>
<p>These estimates separate the two uniformity requirements. For a family of laws, a fixed path with $\rho_\gamma\geq\rho_0&gt;0$ transfers $D_h(x,y)\geq c_0M(h)^2$ with the uniform constant $\rho_0c_0/(\ell+1)$. Any remaining parameters for which $\chi\leq L&lt;\infty$ instead have constant $L^{-2}$. The smaller of these constants works over the union of the two ranges.</p>
<p>For hard distance cutoffs of an intensity kernel, a path retained at all cutoffs $r\geq R$ has a positive uniform opening probability when $\beta\geq\beta_0&gt;0$. Small intensities can be handled by the susceptibility bound when the kernel has a uniformly finite row sum. Bounded cutoff radii still require a uniform susceptibility bound or another argument; their mere boundedness does not establish one. The separated-root interpolation estimate remains a separate input.</p>

## Uniformity for hard distance cutoffs {#section-uniform-cutoff}

<a id="tag-Q6FI" data-assertion="proposition" data-title="A uniform separated-root estimate transfers through every hard cutoff"></a>
<p>On $\mathbb Z^d$, $d\geq1$, let $J(z)=J(-z)\geq0$ have $0&lt;S=\sum_{z\neq0}J(z)&lt;\infty$, and fix $0&lt;B&lt;\infty$. For $0&lt;\beta\leq B$ and $r\geq1$, give distinct vertices $x,y$ bond probability</p>
<div class="math-display">$$q_{\beta,r}(x,y)=\mathbf1_{\{\|x-y\|\leq r\}}\bigl(1-e^{-\beta J(y-x)}\bigr).$$</div>
<p>Suppose there are $R,c_0&gt;0$ such that, for every $\beta,r,h$ in these ranges with $h&gt;0$, and every pair $x,y$ with $\|x-y\|\geq R$,</p>
<div class="math-display">$$D_{\beta,r,h}(x,y)\geq c_0 M_{\beta,r}(h)^2.$$</div>
<p>Then there is $c&gt;0$, independent of $\beta,r,h$, such that</p>
<div class="math-display">$$D_{\beta,r,h}(o,o)\geq c M_{\beta,r}(h)^2.$$</div>
<p><em>Proof.</em> Choose a nonzero displacement $z$ of minimal norm among those with $J(z)&gt;0$. Such a minimum exists because a bounded ball in $\mathbb Z^d$ is finite. Fix an integer $n\geq1$ with $n\|z\|\geq R$, and set</p>
<div class="math-display">$$\beta_0=\min\{B,(2S)^{-1}\},\qquad a=1-e^{-\beta_0J(z)}&gt;0.$$</div>
<p>For $\beta\leq\beta_0$, the off-diagonal bond row sum is at most $\beta S\leq1/2$, uniformly in the cutoff. The <a href="/articles/subcritical-bound/">row-sum susceptibility bound</a> gives $\chi_{\beta,r}\leq2$, so the preceding two-ghost estimate gives $D(o,o)\geq M(h)^2/4$.</p>
<p>Now take $\beta&gt;\beta_0$. If $r&lt;\|z\|$, minimality means that every retained off-diagonal bond has probability zero. Countability makes the root cluster a singleton almost surely, and $D(o,o)=M(h)^2=(1-e^{-h})^2$. If $r\geq\|z\|$, the simple path $0,z,2z,\ldots,nz$ is retained by the cutoff and each of its edges is open with probability at least $a$. Apply the separated-root hypothesis at $0,nz$ and then the finite-path transfer to obtain</p>
<div class="math-display">$$D(o,o)\geq\frac{a^n}{n+1}D(0,nz)\geq\frac{c_0a^n}{n+1}M(h)^2.$$</div>
<p>Thus $c=\min\{1/4,c_0a^n/(n+1)\}$ works in every case. The argument also covers $\beta_0=B$, when the small-intensity case already covers the whole parameter interval.</p>
<p>The endpoint displacement $nz$ can be much longer than the cutoff radius: the proof uses the $n$ short edges of the path, not a single bond joining its endpoints. No susceptibility estimate at a bounded cutoff and large intensity is needed. The theorem is conditional on the uniform separated-root estimate; it does not derive that estimate from the bubble condition.</p>

## Decay of the bubble error {#section-bubble-error}

<a id="tag-3JPN" data-assertion="proposition" data-title="Bubble-error decay with a summable displacement kernel"></a>
<p>Let $t:\mathbb Z^d\to[0,\infty)$ satisfy $\mathcal B=\sum_z t(z)^2&lt;\infty$, and let $J:\mathbb Z^d\to[0,\infty)$ be summable, with $J(0)=0$. Write $a(z)=J(z)^2$, let $*$ denote discrete convolution, and set</p>
<div class="math-display">$$H=t*t,\qquad E(z)=\|a\|_1H(z)+(t*a*t)(z).$$</div>
<p>All these quantities are finite, and</p>
<div class="math-display">$$0\leq E(z)\leq2\mathcal B\|a\|_1,\qquad E(z)\longrightarrow0\quad\text{as }\|z\|\to\infty.$$</div>
<p>Consequently, for every fixed $C&lt;\infty$ there is $R&lt;\infty$ such that $CE(z)\leq1/2$ whenever $\|z\|\geq R$. This same $R$ applies to the corresponding errors for any collection of nonnegative kernels $t_\lambda\leq t$ and $J_\lambda\leq J$.</p>
<p><em>Proof.</em> Summability gives $\|a\|_1\leq\|J\|_1^2&lt;\infty$. Cauchy–Schwarz gives $\|H\|_\infty\leq\|t\|_2^2=\mathcal B$. For a finite set $F$, put $t_F=t\mathbf1_F$. Uniformly in $z$,</p>
<div class="math-display">$$|(t*t)(z)-(t_F*t_F)(z)|\leq\|t-t_F\|_2\bigl(\|t\|_2+\|t_F\|_2\bigr).$$</div>
<p>The right side tends to zero as $F$ exhausts the lattice, while $t_F*t_F$ has finite support. Thus $H$ tends to zero at infinity. Associativity of the nonnegative sums gives $t*a*t=H*a$, and $\|H*a\|_\infty\leq\mathcal B\|a\|_1$. To obtain decay, truncate $a$ to a finite set $A$. The finite sum $H*(a\mathbf1_A)$ tends to zero, and its remainder is uniformly bounded by $\mathcal B\sum_{u\notin A}a(u)$, which can be made arbitrarily small. Adding the two terms proves the assertions. Finally, each convolution and norm factor is monotone in its nonnegative inputs, so all dominated errors are bounded by $E$ itself.</p>
<p>Apply this with $t(z)=\tau_{\beta_c}(0,z)$ when the bubble diagram is finite. Increasing intensity and removing a hard cutoff give the domination $\tau_{\beta,r}\leq\tau_{\beta_c}$, so the separation radius is uniform below criticality and over the cutoffs. If the probabilistic switching argument supplies</p>
<div class="math-display">$$D_{\beta,r,h}(x,y)\geq\bigl[1-CE(y-x)\bigr]M_{\beta,r}(h)^2$$</div>
<p>with a fixed $C$, the conclusion gives the separated-root hypothesis of <a href="/tag/Q6FI/">Q6FI</a> with $c_0=1/2$. The uniform path transfer and <a href="/tag/32MY/">small-field identity</a> then give the backbone comparison wherever susceptibility is finite. This implication does not prove the displayed switching bound: it identifies exactly the remaining probabilistic input in the notes' interpolation argument, lines 3042–3088.</p>

## A cancellation that needs repair {#section-switching-cancellation}

<a id="tag-X4OE" data-assertion="proposition" data-title="A finite obstruction to cancellation in the two-ghost interpolation"></a>
<p>Consider the three-vertex star with centre $o$, leaves $a,b$, and edges $e=\{o,a\}$ and $f=\{o,b\}$. Let $X,Y,F$ be independent Bernoulli-$1/2$ variables. In the first bond configuration the states of $(e,f)$ are $(X,F)$; in the interpolated second configuration they are $(Y,F)$. Independently mark each vertex in each of two fields with probability $1/2$ (ghost intensity $h=\log2$).</p>
<p>Let $H_0$ be the event of two edge-disjoint connections from $o$ to the respective fields in the first configuration. Let $H_1$ require a first-field connection in the first configuration and a second-field connection in the second, disjoint in the underlying product coordinates. Thus both paths may use $e$ in $H_1$, since its two copies are different coordinates, but they cannot both use $f$. Then</p>
<div class="math-display">$$\begin{aligned}
\mathbb P(H_1\setminus H_0,X=0,Y=1)&=16/512,\\
\mathbb P(H_0\setminus H_1,X=1,Y=0)&=15/512,\\
\mathbb P(H_1\setminus H_0,X=Y=1)&=5/512,\\
\mathbb P(H_1)-\mathbb P(H_0)&=6/512.
\end{aligned}$$</div>
<p>In particular, the first two transition probabilities do not cancel, and the total increment is larger than the both-open gain alone.</p>
<p><em>Proof.</em> Condition on $F$ and the six marks. Write $c_{ij}$ for the indicator of $H_1$ when $(X,Y)=(i,j)$. These indicators satisfy $c_{00}\leq c_{10},c_{01}\leq c_{11}$. With $X=0$, the indicator of $H_0$ is $c_{00}$; with $X=1$, it is $\max(c_{10},c_{01})$, since at most one witness may use $e$. Consequently the conditional gain for $(X,Y)=(0,1)$ minus the conditional loss for $(X,Y)=(1,0)$ is</p>
<div class="math-display">$$\frac14\bigl[\min(c_{10},c_{01})-c_{00}\bigr].$$</div>
<p>The bracket is one precisely when $F=1$, neither field marks $o$, and both fields mark both leaves. These seven prescribed bits have probability $2^{-7}$. The difference of the two transition probabilities is therefore $2^{-9}$.</p>
<p>For their individual values, a gain with $(X,Y)=(0,1)$ requires the second field to mark $a$ but not $o$. If the first field marks $o$, the pair $(F,\mathbf1_{\{b\in\mathcal G_2\}})$ can be any pair except $(1,1)$, and its two leaf marks are arbitrary: twelve assignments. If the first field does not mark $o$, it must mark $b$ and have $F=1$; the remaining two leaf marks are arbitrary: four assignments. There are thus sixteen gains among the $512$ equally likely assignments of all nine bits, and the preceding difference gives fifteen losses.</p>
<p>A both-open gain requires neither field to mark $o$ and both to mark $a$. If $F=0$, the two marks at $b$ are arbitrary, giving four assignments. If $F=1$, neither field may mark $b$, giving one more. There are no both-open losses. The states $(X,Y)=(0,0)$ contribute nothing, and the other transition directions cannot occur by increasingness. Subtracting losses from gains gives $(16-15+5)/512=6/512$.</p>
<p>This calculation concerns an intermediate cancellation, not a counterexample to a reverse-BK theorem. The <a href="https://arxiv.org/html/1904.05804v2#S5">proof of Lemma 5.3 in Hutchcroft, <em>The L² boundedness condition in nonamenable percolation</em>, arXiv:1904.05804v2</a>, asserts equality of these two transition probabilities before bounding the both-open gain. That equality cannot be used as stated here. The paper points to Kozma–Nachmias, <em>Arm exponents in high dimensional percolation</em>, Lemma 6.1, for the underlying method. A repaired switching estimate may still give the desired bound with a different argument or constant; the finite example does not settle that question.</p>

## The exact one-coordinate increment {#section-split-identity}

<a id="tag-XWH4" data-assertion="proposition" data-title="Exact increment when one shared coordinate is split"></a>
<p>Let $I$ be finite, let $A,B\subseteq\{0,1\}^I$ be increasing, and distinguish a coordinate $e$ of opening probability $p\in[0,1]$. Give the remaining coordinates any product law $\mu$. Let $A_i,B_i$ be the sections obtained by forcing $e=i$, viewed as events on $I\setminus\{e\}$, and write</p>
<div class="math-display">$$C_{ij}=A_i\circ B_j,\qquad U=C_{10}\cup C_{01},\qquad V=C_{10}\cap C_{01}.$$</div>
<p>Let $H$ be disjoint occurrence with one shared copy of $e$. Let $\widetilde H$ be disjoint occurrence on the enlarged product space in which $A$ uses one copy of $e$ and $B$ an independent copy, both Bernoulli-$p$; all other coordinates remain shared. Then</p>
<div class="math-display">$$\mathbb P(\widetilde H)-\mathbb P(H)=p^2\mu(C_{11}\setminus U)+p(1-p)\mu(V\setminus C_{00}).$$</div>
<p>Both terms are nonnegative. The first is the both-open gain; the second is the excess of the $01$ gain over the $10$ loss. Thus deleting the second term is justified exactly when $p\in\{0,1\}$ or $\mu(V\setminus C_{00})=0$.</p>
<p><em>Proof.</em> Increasingness permits open witnesses throughout. If the shared coordinate is closed, the remaining configuration must lie in $C_{00}$. If it is open, at most one of the two witnesses uses it. The open section is therefore exactly $U$: deleting $e$ from that witness gives one of $C_{10},C_{01}$, and adjoining $e$ to the appropriate witness proves the converse. Hence</p>
<div class="math-display">$$\mathbb P(H)=(1-p)\mu(C_{00})+p\mu(U).$$</div>
<p>With independent copies, the four sections are $C_{00},C_{10},C_{01},C_{11}$, since each witness has its own distinguished coordinate. Consequently</p>
<div class="math-display">$$\mathbb P(\widetilde H)=(1-p)^2\mu(C_{00})+p(1-p)\bigl[\mu(C_{10})+\mu(C_{01})\bigr]+p^2\mu(C_{11}).$$</div>
<p>Use $\mu(C_{10})+\mu(C_{01})=\mu(U)+\mu(V)$ and subtract. Since $C_{00}\subseteq V$ and $U\subseteq C_{11}$, the resulting differences are the measures in the claimed formula. The same calculation conditioned on the remaining configuration identifies the two types of gain.</p>
<p>The identity also applies when some other coordinates have already been split: regard their copies as distinct members of $I$, with each event ignoring the copies assigned to the other. The ghost marks are likewise distinct coordinates for the two fields. In the preceding star example the two terms are $5/512$ and $1/512$.</p>
<p>This identity supplies an exact finite starting point for interpolation. It does not bound the sum of the overlap terms by the bubble diagram, and it gives no uniform reverse-BK estimate by itself. Any such argument must control both terms, or prove a cancellation using additional structure beyond increasingness and independent coordinates.</p>


## What the bubble condition gives in two independent configurations {#section-independent-backbones}

<a id="tag-NGRO" data-assertion="proposition" data-title="Bubble bound for intersections of independent ghost backbones"></a>
<p>Consider two independent copies of an independent-bond model on a countable graph, with common two-point function $\tau$. In copy $i$, independently mark vertices with intensity $h_i&gt;0$, and write $M_i(v)$ for the probability that $v$ reaches its field and $m_i=\sup_v M_i(v)$. Let $\mathcal B_i(x)$ be the union of the vertex sets of all finite simple open paths from $x$ to a vertex marked in field $i$. This set is empty when there is no such connection. Then</p>
<div class="math-display">$$\mathbb P\bigl(\mathcal B_1(x)\cap\mathcal B_2(y)\ne\varnothing\bigr)\leq\sum_z\tau(x,z)\tau(y,z)M_1(z)M_2(z).$$</div>
<p>Consequently, if $Q(x,y)$ is the probability that both sets are nonempty and their vertex sets are disjoint,</p>
<div class="math-display">$$Q(x,y)\geq M_1(x)M_2(y)-m_1m_2\sum_z\tau(x,z)\tau(y,z).$$</div>
<p><em>Proof.</em> If $z\in\mathcal B_i(x)$, a simple open path from $x$ to a marked vertex passes through $z$. Its two segments and its endpoint mark witness $\{x\leftrightarrow z\}\circ\{z\leftrightarrow\mathcal G_i\}$. BK therefore gives $\mathbb P(z\in\mathcal B_i(x))\leq\tau(x,z)M_i(z)$. This includes $z=x$ and a marked endpoint $z$, since empty bond paths are allowed. Independence of the two copies, followed by a union bound over $z$, proves the first inequality. The probability that both sets are nonempty is $M_1(x)M_2(y)$; subtract the intersection probability to obtain the second. On a countable graph every path and mark witness is finite, so finite-coordinate BK and increasing approximation justify the same argument.</p>
<p>In a translation-invariant model with equal ghost intensities, the lower bound becomes $Q(x,y)\geq M(h)^2[1-(\tau*\tau)(y-x)]$. If a family of such laws satisfies $\tau\leq\tau_*$ with $\tau_*\in\ell^2(\mathbb Z^d)$, then $(\tau_* *\tau_*)(z)\to0$ as $\|z\|\to\infty$. Indeed, approximate $\tau_*$ in $\ell^2$ by a finitely supported function and bound the convolution error uniformly by Cauchy–Schwarz. Thus a fixed separation gives $Q(x,y)\geq M(h)^2/2$, uniformly over the family and over $h&gt;0$. Taking $\tau_*=\tau_{\beta_c}$ makes this conclusion uniform over the intensities and hard cutoffs in the notes, under the bubble condition alone.</p>
<p>The two bond configurations here are independent. This is not the one-configuration disjoint event $D_h(x,y)$ used in the backbone-count limit. A comparison $D_h(x,y)\geq c_*Q(x,y)$ with a uniform positive constant would complete the separated-root step and, by <a href="/tag/Q6FI/">the cutoff transfer</a>, the requested backbone comparison. Such a comparison has not been established here. Selecting or combining paths from the two copies does not by itself preserve the one-configuration product law.</p>

## A replacement under the triangle condition {#section-triangle-replacement}

<a id="tag-DTVY" data-assertion="theorem" data-title="Distinct green clusters with a triangle-convolution error"></a>
<p>Consider independent bond percolation on a countable simple graph, with arbitrary edge probabilities in $[0,1]$. Write $\tau(x,y)=\mathbb P(x\leftrightarrow y)$ and</p>
<div class="math-display">$$T^3(x,y)=\sum_{u,v}\tau(x,u)\tau(u,v)\tau(v,y).$$</div>
<p>Let $\mathcal G_1,\ldots,\mathcal G_\ell$ be independent vertex ghost fields of intensities $h_i&gt;0$, independent of the bonds. Put $M_i(v)=\mathbb P(v\leftrightarrow\mathcal G_i)$ and $m_i=\sup_v M_i(v)$. For roots $x_1,\ldots,x_\ell$, let $D_\ell$ be the event that their clusters are pairwise distinct and each $K_{x_i}$ meets $\mathcal G_i$. If the triangle convolutions between distinct indexed roots are finite, then</p>
<div class="math-display">$$\mathbb P(D_\ell)\geq\prod_{i=1}^\ell M_i(x_i)-\left(\prod_{i=1}^\ell m_i\right)\sum_{1\leq i&lt;j\leq\ell}T^3(x_i,x_j).$$</div>
<p>No transitivity, finite degree or restriction away from edge probabilities zero and one is needed. When the law is transitive and the fields have common intensity $h$, the right side is $M(h)^\ell[1-\sum_{i&lt;j}T^3(x_i,x_j)]$.</p>
<p><em>Proof.</em> Work first on a finite graph. For a deterministic vertex set $S$, let $M_i^{G\setminus S}(y)$ be the magnetization after deleting $S$, with value zero if $y\in S$. Couple the deleted graph to the original one. A connection destroyed by the deletion has a simple open path to a marked vertex that passes through some $z\in S$. Splitting that path at $z$ and applying BK gives</p>
<div class="math-display">$$M_i(y)-M_i^{G\setminus S}(y)\leq\sum_{z\in S}\tau(y,z)M_i(z).$$</div>
<p>Let $E_k=D_k$ for the first $k$ roots and fields. Reveal their clusters and put $S=\bigcup_{j\leq k}K_{x_j}$. All bonds within $V\setminus S$ retain their independent law conditional on this exploration. The new field is independent of the exploration and the preceding fields. Therefore</p>
<div class="math-display">$$\mathbb P(E_{k+1})=\mathbb E\left[\mathbf1_{E_k}M_{k+1}^{G\setminus S}(x_{k+1})\right].$$</div>
<p>The deletion bound shows that the deficit from $\mathbb P(E_k)M_{k+1}(x_{k+1})$ is at most</p>
<div class="math-display">$$\sum_{j\leq k}\sum_z\tau(x_{k+1},z)M_{k+1}(z)\,\mathbb P(E_k,\ z\in K_{x_j}).$$</div>
<p>On $E_k\cap\{z\in K_{x_j}\}$, choose a marked vertex of the $j$th field in $K_{x_j}$. A tree connecting it to $x_j$ and $z$ has a branch point $w$ and three edge-disjoint paths. Each other cluster supplies a path from its root to its own field, disjoint from this tree and from the other paths. The ghost marks belong to distinct fields, so their witness coordinates are also disjoint. BK and a union bound over $w$ imply</p>
<div class="math-display">$$\mathbb P(E_k,\ z\in K_{x_j})\leq\sum_w\tau(x_j,w)\tau(w,z)M_j(w)\prod_{\substack{i\leq k\\i\ne j}}M_i(x_i).$$</div>
<p>Paths of length zero handle coincident branch points. Substitute this estimate into the deficit and bound each magnetization by its supremum. The additional error is at most $(\prod_{i\leq k+1}m_i)\sum_{j\leq k}T^3(x_j,x_{k+1})$. Starting with $\mathbb P(E_1)=M_1(x_1)$ proves the assertion by induction.</p>
<p>For a countable graph, exhaust its vertices by finite sets and retain only edges with both endpoints in the set. The restricted connection probabilities and magnetizations increase to their full values and are bounded by them. The indicators of $D_\ell$ converge almost surely: any two roots connected in the full graph eventually have a finite connecting path in the exhaustion; for distinct full clusters, each ghost hit likewise has a finite witness. If a required ghost hit does not occur in the full graph, it never occurs in the exhaustion. Dominated convergence for these indicators and the uniform full-graph upper bounds on the error give the result.</p>
<p>This replaces the cancellation argument by cluster exploration and a three-branch decomposition. It gives distinct clusters directly, but the error is $T^3$, not $T^2$. Thus it does not repair the bubble-only estimate. The remaining section explains why the stronger input is nevertheless enough for the high-dimensional multiple-arm conclusion.</p>

## Recovering the high-dimensional multiple-arm lower bound {#section-multiple-arm-replacement}

<a id="tag-79WX" data-assertion="corollary" data-title="Separated multiple arms from triangle decay and a volume tail"></a>
<p>Let $d&gt;6$ be an integer and consider a translation-invariant independent bond law on a finite-range graph on $\mathbb Z^d$. Suppose, for fixed positive constants,</p>
<div class="math-display">$$\tau(0,x)\leq C(1+\|x\|_\infty)^{2-d},\qquad c n^{-1/2}\leq\mathbb P(|K_0|\geq n)\leq C n^{-1/2}\quad(n\geq1).$$</div>
<p>For every integer $\ell\geq1$ there are $K&lt;\infty$ and $c_\ell&gt;0$ such that, for every integer $r\geq1$ and roots $x_1,\ldots,x_\ell\in Q_{r/2}$ with pairwise $\ell^\infty$ distances at least $K$,</p>
<div class="math-display">$$\mathbb P\left(\mathop{\circ}_{i=1}^\ell\{x_i\leftrightarrow\mathbb Z^d\setminus Q_r\}\right)\geq c_\ell r^{-2\ell},\qquad Q_t=\{x:\|x\|_\infty\leq t\}.$$</div>
<p><em>Proof.</em> Summing the power kernels gives $T^3(0,x)\leq C'(1+\|x\|_\infty)^{6-d}$. One way to check the convolution estimate is to split a sum of kernels with powers $a-d,b-d$, where $a,b&gt;0$ and $a+b&lt;d$, into the regions within half the separation of either endpoint and their complement. Summing shells in these three regions gives a bound of order $(1+\|x\|_\infty)^{a+b-d}$. Apply this first with $a=b=2$, then with $a=4,b=2$.</p>
<p>The volume-tail bounds imply $c'\sqrt h\leq M(h)\leq C'\sqrt h$ for $0&lt;h\leq1$. Indeed, if $N=|K_0|$, tail summation gives</p>
<div class="math-display">$$M(h)=(1-e^{-h})\sum_{n\geq1}e^{-h(n-1)}\mathbb P(N\geq n),$$</div>
<p>and comparison with the integral of $e^{-ht}t^{-1/2}$ gives the asserted bounds. Choose $K$ so large that $\sum_{i&lt;j}T^3(x_i,x_j)\leq1/2$. By DTVY, the probability of distinct clusters all meeting their respective independent fields is at least $M(h)^\ell/2$.</p>
<p>If one of these clusters fails to leave $Q_r$, its field connection ends in $Q_r$. The two-point bound, uniformly for $x_i\in Q_{r/2}$, gives</p>
<div class="math-display">$$\mathbb P(x_i\leftrightarrow\mathcal G_i\cap Q_r)\leq h\sum_{z\in Q_r}\tau(x_i,z)\leq C''hr^2.$$</div>
<p>On the distinct-cluster event this connection has a witness disjoint from the other $\ell-1$ field connections. BK and a union bound thus bound the probability of any such failure by $\ell C''hr^2M(h)^{\ell-1}$. All remaining configurations have disjoint arms leaving $Q_r$. Set $h=\varepsilon r^{-4}$, with $0&lt;\varepsilon\leq1$. The lower bound on $M$ yields</p>
<div class="math-display">$$\mathbb P\left(\mathop{\circ}_{i=1}^\ell\{x_i\leftrightarrow\mathbb Z^d\setminus Q_r\}\right)\geq M(h)^\ell\left(\frac12-\frac{\ell C''}{c'}\sqrt\varepsilon\right).$$</div>
<p>Choose $\varepsilon$ sufficiently small, depending only on the displayed constants and $\ell$, to make the bracket at least $1/4$. Since $M(h)^\ell\geq(c')^\ell\varepsilon^{\ell/2}r^{-2\ell}$, the conclusion follows.</p>
<p>The hypotheses are supplied by equations (1.1)–(1.2) in <a href="https://arxiv.org/pdf/0911.0871v1#page=3">Kozma–Nachmias, <em>Arm exponents in high dimensional percolation</em>, arXiv:0911.0871v1</a>. Together with their one-arm upper bound and BK, this recovers the multiple-arm estimate of Theorem 3 without their Lemma 6.1. In the <a href="https://arxiv.org/pdf/0911.0871v1#page=39">arXiv proof of that lemma</a>, swapping the selected edge copies is asserted to map the gain event onto the loss event. The overlap term in XWH4 is not removed by this assertion. The replacement here uses triangle decay and the volume tail; it neither validates that bijection nor establishes a reverse estimate from bubble convergence alone.</p>

## Adding one edge to the backbone count {#section-edge-increment}

<p>For a finite open cluster $C$, use the same edge-disjoint count $B_C$ as in <a href="/tag/EJHT/">EJHT</a>, and put $T_u^C=\sum_{v\in C}B_C(u,v)$ and $F(C)=\sum_{u\in C}T_u^C$. The diagonal $B_C(u,u)$ is retained; it can exceed one when there are cycles.</p>

<a id="tag-K9H7" data-assertion="proposition" data-title="Bridge addition and the within-cluster increment of the backbone functional"></a>
<p>Let $e=\{a,b\}$ be a closed edge of a finite configuration. If its endpoints lie in distinct clusters $A,B$, then opening it changes $\sum_C F(C)$ by</p>
<div class="math-display">$$2\bigl[|B|T_a^A+|A|T_b^B\bigr].$$</div>
<p>If its endpoints already lie in one cluster $C$, the change is instead $\Gamma_{ab}=F(C+e)-F(C)\geq0$.</p>
<p><em>Proof.</em> The new edge is a bridge when the clusters are distinct. A backbone vertex for two endpoints in $A$ cannot lie in $B$: both witness paths would have to use the bridge. Nor can a simple witness with endpoints in $A$ leave $A$ and return across the sole bridge. Thus the within-cluster counts are unchanged. For $u\in A$, $v\in B$, splitting according to which side contains the counted vertex gives exactly</p>
<div class="math-display">$$B_{A\cup B+e}(u,v)=B_A(u,a)+B_B(b,v).$$</div>
<p>The bridge can be appended to the appropriate witness in either direction, and every cross-cluster witness uses it in exactly one of its two paths. Sum over the ordered cross-cluster pairs and use $B_C(u,v)=B_C(v,u)$ to obtain the formula. In the within-cluster case, edge addition preserves every old witness, proving $\Gamma_{ab}\geq0$.</p>
<p>The second case cannot be discarded. Opening the missing edge of a triangle changes the backbone counts, including the diagonal counts, although all three vertices were already connected.</p>

## The finite-volume derivative {#section-finite-generator}

<a id="tag-GKBQ" data-assertion="theorem" data-title="Finite-group backbone derivative with the closed cycle term retained"></a>
<p>Let $H$ be a finite group. At parameter $t$ in an open interval, give the unordered pair $\{x,y\}$, $x\ne y$, intensity $k_t(x^{-1}y)$, where $k_t(g)=k_t(g^{-1})\geq0$ is finite, nondecreasing and locally absolutely continuous. Open the pairs independently with probabilities $1-e^{-k_t(x^{-1}y)}$. Write $w_t(g)=\dot k_t(g)$ where the derivatives exist, $\chi=\mathbb E|K_o|$, $S=\mathbb E T_o$, and $T_u=T_u^{K_u}$. Then $\chi,S$ are locally absolutely continuous and, almost everywhere,</p>
<div class="math-display">$$\begin{aligned}
\chi'&=\sum_{y\ne o}w_t(y)\,\mathbb E\bigl[|K_o||K_y|\mathbf1_{\{o\not\leftrightarrow y\}}\bigr],\\
S'&=2\sum_{y\ne o}w_t(y)\,\mathbb E\bigl[T_o|K_y|\mathbf1_{\{o\not\leftrightarrow y\}}\bigr]+\mathcal C_t,\\
\mathcal C_t&=\frac12\sum_{y\ne o}w_t(y)\,\mathbb E\bigl[\mathbf1_{\{\omega_{\{o,y\}}=0,\ o\leftrightarrow y\}}\Gamma_{oy}\bigr]\geq0.
\end{aligned}$$</div>
<p>Define $\Gamma_{oy}=0$ outside the event in its indicator. Both cluster factors in each expectation refer to the same configuration.</p>
<p><em>Proof.</em> For any real function $f$ of a finite bond configuration, finite-product differentiation gives</p>
<div class="math-display">$$\frac{d}{dt}\mathbb E f=\sum_{e=\{a,b\}}\dot k_t(a^{-1}b)\,
\mathbb E\bigl[\mathbf1_{\{\omega_e=0\}}(f(\omega+e)-f(\omega))\bigr].$$</div>
<p>Indeed, the derivative of the edge probability is $\dot k_t(a^{-1}b)e^{-k_t(a^{-1}b)}$; the closed-edge indicator supplies exactly the exponential factor. A finite expectation is a polynomial in the edge probabilities, so the chain rule also gives local absolute continuity.</p>
<p>Apply this formula to $|H|^{-1}\sum_C|C|^2$ and $|H|^{-1}\sum_C F(C)$. Their expectations are $\chi$ and $S$ by invariance. Joining distinct clusters changes the first sum by $2|A||B|$ and the second by <a href="/tag/K9H7/">K9H7</a>; opening an edge inside a cluster changes only the second, by $\Gamma_{ab}$. Convert the unordered-edge sum to half the ordered-edge sum and translate its first endpoint to $o$. The two bridge terms for $F$ agree after reversing the ordered pair, giving the coefficient two in $S'$. The cycle term retains the factor one half and its closed-edge indicator.</p>

## The normalized deficit identity {#section-normalized-deficit}

<a id="tag-JFE6" data-assertion="proposition" data-title="Normalized backbone derivative as a difference of deficits plus a cycle term"></a>
<p>In <a href="/tag/GKBQ/">GKBQ</a>, put $a_t=\sum_{y\ne o}w_t(y)$. At almost every parameter with $a_t&gt;0$, define</p>
<div class="math-display">$$\begin{aligned}
\mathcal E_1&=1-\frac{\sum_{y\ne o}w_t(y)\mathbb E[|K_o||K_y|\mathbf1_{\{o\not\leftrightarrow y\}}]}{a_t\chi^2},\\
\mathcal E_S&=1-\frac{\sum_{y\ne o}w_t(y)\mathbb E[T_o|K_y|\mathbf1_{\{o\not\leftrightarrow y\}}]}{a_t\chi S}.
\end{aligned}$$</div>
<p>Both deficits lie in $[0,1]$. For $W=S/\chi^2$,</p>
<div class="math-display">$$W'=2a_t\chi W(\mathcal E_1-\mathcal E_S)+\frac{\mathcal C_t}{\chi^2}.$$</div>
<p>When $a_t=0$, every intensity derivative vanishes and $W'=0$ almost everywhere on that set.</p>
<p><em>Proof.</em> On $\{o\not\leftrightarrow y\}$, a connection witness in $K_o$ is edge-disjoint from every connection witness in $K_y$. Expanding the two cluster sizes and applying BK therefore gives $\mathbb E[|K_o||K_y|\mathbf1_{\{o\not\leftrightarrow y\}}]\leq\chi^2$. Likewise expand $T_o$ as a sum of the two-arm indicators defining $B(o,x)$. Each such event has all its witnesses in $K_o$, disjoint from a witness for $y\leftrightarrow v$ in $K_y$. BK between these two events gives</p>
<div class="math-display">$$\mathbb E[T_o|K_y|\mathbf1_{\{o\not\leftrightarrow y\}}]\leq S\chi.$$</div>
<p>Nonnegativity proves the other side of each deficit bound. Substituting their definitions in GKBQ yields $\chi'=a_t\chi^2(1-\mathcal E_1)$ and $S'=2a_t\chi S(1-\mathcal E_S)+\mathcal C_t$. Differentiate $S/\chi^2$; since $\chi,S\geq1$, the quotient and all denominators are well defined. The claimed identity follows.</p>
<p>For a radial soft cutoff $k_r(y)=\beta_c\mathbf1_{\{0&lt;\|y\|\leq r\}}\int_{\|y\|}^r|J'(s)|\,ds$, the weights are $w_r(y)=\beta_c|J'(r)|\mathbf1_{\{0&lt;\|y\|\leq r\}}$ almost everywhere. The finite identities show exactly which terms an infinite-volume argument must retain. Passing to the lattice requires convergence of the integrated generator expressions, including the cycle term; it does not follow solely from convergence of the observables. <a href="https://github.com/tomhutchcroft/lrp/issues/242#issuecomment-6902840243">FIXER's record</a> gives the proposed moment-domination justification for that passage. The tagged derivative theorem here is finite-volume.</p>

## A sufficient estimate for strong comparability {#section-additive-criterion}

<a id="tag-TJXV" data-assertion="proposition" data-title="An additive integrable derivative bound upgrades a logarithmic lower bound"></a>
<p>Let $W:[R_0,\infty)\to(0,1]$ be locally absolutely continuous, where $R_0&gt;1$. Suppose there are $c&gt;0$ and $C\geq0$ such that</p>
<div class="math-display">$$W(r)\geq\frac{c}{\sqrt{\log r}}\quad(r\geq R_0),\qquad
W'(r)\geq-\frac{C}{r(\log r)^2}\quad\text{for almost every }r\geq R_0.$$</div>
<p>Then $W$ is bounded below by a positive constant on some terminal interval.</p>
<p><em>Proof.</em> For $r\geq R\geq R_0$, integration gives</p>
<div class="math-display">$$W(r)\geq W(R)-C\left(\frac1{\log R}-\frac1{\log r}\right)
\geq\frac{c}{\sqrt{\log R}}-\frac{C}{\log R}.$$</div>
<p>Choose one fixed $R$ with $\sqrt{\log R}&gt;2C/c$. The last expression is at least $c/(2\sqrt{\log R})$, uniformly for all $r\geq R$.</p>
<p>Applied to $W_r=S_r/\chi_r^2$, the moment inputs in <a href="/tag/44CZ/">44CZ</a> supply the lower bound and BK supplies $W_r\leq1$. The missing estimate is the displayed derivative lower bound for this particular observable. Neither the volume moments nor a bound on $\mathcal E_1$ alone supplies it: the normalized identity contains $\mathcal E_S$ and the cycle contribution as well. An error merely $o(1/(r\log r))$ would not suffice; for large $r$, $W(r)=1/\log\log r$ satisfies the weaker derivative estimate and the logarithmic lower bound but tends to zero.</p>
<p>Thus the critical-dimensional conclusion $S_r\asymp\chi_r^2\asymp r^{2\alpha}$ remains open in the <a href="https://github.com/tomhutchcroft/lrp/issues/242#issuecomment-6902840243">FIXER investigation</a>. These results document its starting bounds and reduction, not a proof of the missing cancellation or of the bubble-only reverse-BK theorem.</p>

## What the bubble condition still has to supply {#section-source}

<p>The notes, lines 2965–3133 (S019), use this observable and a two-ghost reverse-BK bound to obtain backbone scaling under a bubble condition. The counting identity, upper bound, small-field limit, finite-path transfer and analytic error decay are proved here. The uniform reverse-BK estimate itself is not established by these arguments.</p>
<p>Its proof must still establish the probabilistic switching bound with a constant uniform in the intensity and cutoff. The convolution argument above proves decay of its proposed error expression, not the switching bound itself. For the stated summable displacement kernels with hard distance cutoffs, the uniform transfer is now supplied above, conditional on the separated-root estimate. Positivity of a connecting edge at a fixed parameter does not by itself give a uniform finite-energy constant as the intensity tends to zero, and a spatial cutoff may remove that edge. Those uniformity issues need their own estimates. This article neither asserts a counterexample to the source proposition nor treats its reverse estimate as proved.</p>

<p>The <a href="https://github.com/tomhutchcroft/lrp/issues/242#issuecomment-6903148948">subsequent FIXER follow-up</a> records a continuous-interpolation route, a mixed-moment upper bound and a covariance reformulation of the cutoff cancellation. It also explains why the remaining connecting paths cannot simply be factored. Neither the required accumulated-overlap estimate nor the signed derivative bound has been established. These are further reductions for the unresolved target; the conditional long-range multipoint bound in <a href="/tag/2BBE/">2BBE</a> uses separate cutoff inputs and does not assume a reverse-BK repair.</p>

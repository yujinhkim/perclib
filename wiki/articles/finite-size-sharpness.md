---
{
  "id": "finite-size-sharpness",
  "title": "Sharpness from the boundary functional",
  "subtitle": "Finite boundary wiring, a pivotal identity, and threshold identification",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "Summable long-range boundary intensities can be wired into a finite graph. Its closed-pivotal identity gives the supercritical inequality, which identifies the finite-size threshold and proves subcritical finite susceptibility.",
  "context": ["A countable vertex set $V$, with a fixed root $o$.", "Finite nonnegative symmetric off-diagonal weights $J_{uv}$ with $\\sum_{v\\ne u}J_{uv}<\\infty$ for each $u$.", "Independent bond probabilities $q_\\beta(u,v)=1-e^{-\\beta J_{uv}}$, for finite $\\beta\\geq0$; diagonal coordinates do not affect the graph.", "Transitivity is assumed only in the threshold theorem."],
  "related": ["sharpness", "boundary-laws", "russo-formula", "finite-volume", "bk-inequality"],
  "sourceIds": ["notes"],
  "aliases": ["finite-size threshold", "Duminil-Copin Tassion", "closed pivotal", "supercritical lower bound", "sharpness"],
  "prototypeUses": []
}
---

## Wire a finite domain {#section-wiring}

<p>For a finite $\Lambda\ni o$, set $f_\Lambda(\beta)=\mathbb P_\beta(K_o\not\subseteq\Lambda)$. Retain all bonds inside $\Lambda$ and replace the exterior by a single vertex $g$. Give the bond $\{u,g\}$ intensity</p>
<div class="math-display">$$j_\Lambda(u)=\sum_{v\notin\Lambda}J_{uv},\qquad u\in\Lambda.$$</div>
<p>These are finite numbers. By the <a href="/tag/AGF6/">independent boundary-block law</a> and its <a href="/tag/ZANA/">exponential marginal</a>, the finite graph on $\Lambda\cup\{g\}$ has the same joint law of internal bonds and boundary indicators as the original model. Moreover, $o$ connects to $g$ exactly when an internal path from $o$ reaches an open boundary bond, which is equivalent to exiting $\Lambda$ in the original model. Thus $f_\Lambda$ is a finite-product event probability and is continuously differentiable for $\beta&gt;0$, with a right derivative at zero. This reduction does not require finite range.</p>

## The region not reached from the boundary {#section-pivotal}

<a id="tag-HATE" data-assertion="theorem" data-title="Exact wired boundary derivative and finite-size differential inequality"></a>
<p>In the wired finite graph, let $S$ be the random subset of $\Lambda$ consisting of the vertices not connected to $g$. For a deterministic finite $T\ni o$, put</p>
<div class="math-display">$$W_\beta(o,T)=\sum_{u\in T}\tau_{T,\beta}(o,u)\sum_{v\notin T}J_{uv},\qquad \Phi_\beta(o,T)=\sum_{u\in T}\tau_{T,\beta}(o,u)\sum_{v\notin T}(1-e^{-\beta J_{uv}}).$$</div>
<p>Here $\tau_{T,\beta}$ is the internal connection probability in $T$. Then</p>
<div class="math-display">$$f_\Lambda'(\beta)=\sum_{\substack{T\subseteq\Lambda\\o\in T}}\mathbb P_\beta(S=T)W_\beta(o,T).$$</div>
<p>The identity holds for $\beta&gt;0$ and for the right derivative at zero. In particular, for $\beta&gt;0$,</p>
<div class="math-display">$$f_\Lambda'(\beta)\geq\frac{1-f_\Lambda(\beta)}{\beta}\min_{\substack{T\subseteq\Lambda\\o\in T}}\Phi_\beta(o,T).$$</div>
<p><em>Proof.</em> The event $S=T$ is determined by two requirements: all bonds from $T$ to $(\Lambda\setminus T)\cup\{g\}$ are closed, and every vertex of $\Lambda\setminus T$ connects to $g$ using only that complement and $g$. Neither requirement reads a bond with both endpoints in $T$. Conversely, these requirements imply $S=T$. Independence therefore gives, for $u\in T$,</p>
<div class="math-display">$$\mathbb P_\beta(S=T,\ o\leftrightarrow_T u)=\mathbb P_\beta(S=T)\tau_{T,\beta}(o,u).$$</div>
<p>This factorization also holds when $\mathbb P_\beta(S=T)=0$; no conditional probability at a null event is needed.</p>
<p>When $o\in S$, a closed bond is pivotal for $o\leftrightarrow g$ exactly when it joins a vertex $u\in S$ internally connected to $o$ to a vertex outside $S$. The outside endpoint already connects to $g$ without entering $S$. Bonds with both endpoints on one side cannot join the root's component to the boundary component. If $o\notin S$, the event already holds and no closed bond is pivotal.</p>
<p>Apply the <a href="/tag/IENL/">finite intensity Russo formula</a>, using closed pivotality. On $S=T$, the sum of intensities of possible pivotal bonds leaving $u\in T$ is</p>
<div class="math-display">$$\sum_{v\in\Lambda\setminus T}J_{uv}+j_\Lambda(u)=\sum_{v\notin T}J_{uv}.$$</div>
<p>The preceding factorization gives the exact derivative. Finally $1-e^{-\beta J_{uv}}\leq\beta J_{uv}$ implies $W_\beta(o,T)\geq\Phi_\beta(o,T)/\beta$, and</p>
<div class="math-display">$$\sum_{\substack{T\subseteq\Lambda\\o\in T}}\mathbb P_\beta(S=T)=\mathbb P_\beta(o\not\leftrightarrow g)=1-f_\Lambda(\beta).$$</div>
<p>The claimed inequality follows. All differentiation and conditioning identities took place in a finite graph.</p>

## Identify the threshold {#section-threshold}

<a id="tag-L0TE" data-assertion="theorem" data-title="Sharpness and the supercritical density bound for transitive summable intensities"></a>
<p>Assume in addition that a group of vertex permutations acts transitively and preserves the weights. Define the extended thresholds</p>
<div class="math-display">$$t=\inf\{\beta\geq0:\Phi_\beta(o,T)\geq1\text{ for every finite }T\ni o\},\qquad \beta_c=\inf\{\beta\geq0:\mathbb P_\beta(|K_o|=\infty)&gt;0\},$$</div>
<p>with $\inf\varnothing=\infty$. Then $t=\beta_c$. For every finite $0\leq\beta&lt;\beta_c$, the susceptibility $\chi_\beta(o)$ is finite. If $\beta_c&lt;\infty$, then for every finite $\beta&gt;\beta_c$,</p>
<div class="math-display">$$\mathbb P_\beta(|K_o|=\infty)\geq1-\frac{\beta_c}{\beta}.$$</div>
<p>For finite $\beta_c$, this also gives $\mathbb P_\beta(|K_o|=\infty)\geq (\beta_c+1)^{-1}\min\{\beta-\beta_c,1\}$ when $\beta&gt;\beta_c$. The root threshold equals the threshold defined by positive probability of an infinite cluster anywhere.</p>
<p><em>Proof.</em> Each function $\beta\mapsto\Phi_\beta(o,T)$ is nondecreasing, since both its internal connection probabilities and its bond probabilities are nondecreasing. Hence the set in the definition of $t$ is an upper set. If $\beta&lt;t$, some finite $T\ni o$ has $\Phi_\beta(o,T)&lt;1$. Transitivity transports this set to every root. The <a href="/tag/YLZV/">finite-size susceptibility criterion</a> gives</p>
<div class="math-display">$$\chi_\beta(o)\leq\frac{\sum_{u\in T}\tau_{T,\beta}(o,u)}{1-\Phi_\beta(o,T)}&lt;\infty.$$</div>
<p>Thus $\beta_c\geq t$. If $t=\infty$, this already proves equality and finite susceptibility at every finite intensity.</p>
<p>Suppose now $t&lt;\infty$. Every $s&gt;t$ belongs to the upper set defining $t$: by the definition of its infimum there is an element below $s$, and upper closure then includes $s$. Therefore all the finite sets in the minimum of the preceding differential inequality have boundary functional at least one at such $s$. For any $\beta&gt;a&gt;t$ with $a&gt;0$,</p>
<div class="math-display">$$f_\Lambda'(s)\geq\frac{1-f_\Lambda(s)}s\quad(a\leq s\leq\beta),\qquad (s f_\Lambda(s))'\geq1.$$</div>
<p>Integrating and using $f_\Lambda(a)\geq0$ gives $\beta f_\Lambda(\beta)\geq\beta-a$. Let $a\downarrow t$ to obtain $f_\Lambda(\beta)\geq1-t/\beta$.</p>
<p>Exhaust $V$ by increasing finite domains $\Lambda_n\ni o$. A cluster exits every such domain exactly when it is infinite, so the escape events decrease to $\{|K_o|=\infty\}$. Continuity of probability from above yields</p>
<div class="math-display">$$\mathbb P_\beta(|K_o|=\infty)=\lim_n f_{\Lambda_n}(\beta)\geq1-\frac t\beta&gt;0\qquad(\beta&gt;t).$$</div>
<p>Consequently $\beta_c\leq t$, proving equality and the stated density bound. Writing $\delta=\beta-\beta_c$, the elementary bound $\delta/(\beta_c+\delta)\geq\min\{\delta,1\}/(\beta_c+1)$ gives the second density estimate. Finally, transitivity makes every root's infinite-cluster probability the same, while countability makes the event of an infinite cluster anywhere a countable union of root events. Positive probability occurs for that union exactly when it occurs at the fixed root.</p>
<p>The proof permits a zero kernel and finite host components, in which case the threshold may be infinite. It does not assert absence of an infinite cluster at $\beta_c$, exponential decay in ambient distance, or critical exponent asymptotics. Finite susceptibility throughout the strict subcritical interval and the displayed supercritical lower bound are the conclusions proved here.</p>

<p>The notes' sharpness statement also includes an exponential cluster-volume tail. That requires a separate moment-to-tail argument after finite susceptibility is known. Its printed bound with unit prefactor at every $n\geq1$ needs correction: $|K_o|\geq1$ surely, whereas $e^{-c}&lt;1$ for $c&gt;0$. A valid statement must retain a suitable prefactor, shift the threshold, or restrict to sufficiently large $n$.</p>

## Where susceptibility diverges {#section-divergence}

<a id="tag-RDF0" data-assertion="corollary" data-title="Finite-set contraction characterizes finite susceptibility and gives critical blow-up"></a>
<p>Under the transitive summable-intensity assumptions above, at each finite $\beta\geq0$ the following are equivalent: $\chi_\beta(o)&lt;\infty$; some finite $T\ni o$ satisfies $\Phi_\beta(o,T)&lt;1$; and $\beta&lt;\beta_c$. In particular, if $\beta_c&lt;\infty$, then</p>
<div class="math-display">$$\chi_{\beta_c}(o)=\infty,\qquad \lim_{\beta\uparrow\beta_c}\chi_\beta(o)=\infty.$$</div>
<p><em>Proof.</em> The finite-size criterion proves that contraction implies finite susceptibility, and the threshold theorem gives finite susceptibility below $\beta_c$. Suppose conversely that $\chi_\beta(o)&lt;\infty$, and exhaust $V$ by finite sets $T_n\ni o$. Write $Q_\beta=\sum_{v\ne u}q_\beta(u,v)$ for the common finite probability row sum. Since internal connections imply unrestricted connections,</p>
<div class="math-display">$$0\leq\Phi_\beta(o,T_n)\leq\sum_{u\in V}\tau_\beta(o,u)\mathbf1_{\{u\in T_n\}}\sum_{v\notin T_n}q_\beta(u,v).$$</div>
<p>For each fixed $u$, the exterior row tail tends to zero. The summand is bounded by $Q_\beta\tau_\beta(o,u)$, whose sum is $Q_\beta\chi_\beta(o)&lt;\infty$. Dominated convergence therefore gives $\Phi_\beta(o,T_n)\to0$, and some $T_n$ contracts. By the continuity and transitivity argument in the <a href="/tag/R84Z/">critical-flux theorem</a>, contraction at $\beta$ persists at a strictly larger intensity with finite susceptibility. Thus $\beta&lt;\beta_c$. This also proves $\chi_{\beta_c}(o)=\infty$ when the critical point is finite.</p>
<p>For the left limit, retain any finite edge set $F$. Its susceptibility $\chi_{F,\beta}(o)$ is continuous in $\beta$ and bounded above by $\chi_\beta(o)$. Consequently</p>
<div class="math-display">$$\chi_{F,\beta_c}(o)\leq\lim_{\beta\uparrow\beta_c}\chi_\beta(o).$$</div>
<p>Let $F$ increase to all possible edges. Finite-path approximation and monotone convergence make the left side tend to $\chi_{\beta_c}(o)=\infty$, proving the claim. The left limit exists by monotonicity. The finite critical point is positive: for the common intensity row mass $M$, a singleton has $\Phi_\beta(o,\{o\})\leq\beta M$, and hence contracts for sufficiently small $\beta$; if $M=0$, the threshold is infinite instead.</p>
<p>Divergence of the expected volume does not decide whether an infinite cluster occurs at the critical intensity. That probability remains a separate question.</p>

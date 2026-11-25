---
{
  "id": "covariance-russo",
  "title": "Russo's formula in covariance form",
  "subtitle": "Exact coefficients and conditional revealment bounds",
  "kind": "theorem",
  "category": "Foundations",
  "summary": "Coordinate covariances express finite-product derivatives; a supplied revealment inequality then yields a quantitative derivative lower bound.",
  "context": ["A finite coordinate set $E$ with independent Bernoulli bits $X_e$.", "Finite nonnegative weights $J_e$ and finite intensity $\\beta$.", "Increasingness is required for nonnegative covariance bounds, not for the identities."],
  "related": ["russo-formula", "harris-inequality", "finite-transcripts"],
  "sourceIds": ["notes"],
  "aliases": ["coordinate covariance", "Russo covariance formula", "revealment derivative bound"],
  "prototypeUses": ["russo-formula"]
}
---

## Coordinate covariances {#section-coordinate}

<a id="tag-VVDC" data-assertion="proposition" data-title="Coordinate covariance identity"></a>
<p>Let $q\in[0,1]^E$ and let $f:\{0,1\}^E\to\mathbb R$. With the coordinate increment $\Delta_e f$ of <a href="/tag/71GK/">71GK</a>,</p>
<div class="math-display">$$\operatorname{Cov}_q(f,X_e)=q_e(1-q_e)\,\mathbb E_q[\Delta_e f].$$</div>
<p>This identity includes $q_e=0$ and $q_e=1$. In particular, the covariance is nonnegative when $f$ is increasing.</p>
<p><em>Proof.</em> Average the two forced values of $f$ over the other coordinates, obtaining $a=\mathbb E_q[f(\omega^{e,1})]$ and $b=\mathbb E_q[f(\omega^{e,0})]$. Independence gives $\mathbb E_q[fX_e]=q_ea$ and $\mathbb E_q[f]=q_ea+(1-q_e)b$. Subtraction gives $q_e(1-q_e)(a-b)$, and $a-b=\mathbb E_q[\Delta_e f]$. No conditioning on a null event is needed.</p>
<p>For an increasing event $A$, the increment is its pivotal indicator. Thus the covariance is $q_e(1-q_e)$ times the pivotal probability, not the closed-pivotal probability.</p>

## Intensity coefficients {#section-intensity}

<a id="tag-DUYN" data-assertion="proposition" data-title="Exact covariance coefficients for finite intensity derivatives"></a>
<p>Put $q_\beta(e)=1-e^{-\beta J_e}$, where $0\leq J_e&lt;\infty$, and let $E_+=\{e:J_e&gt;0\}$. For $0&lt;\beta&lt;\infty$ and any real observable $f$ on the finite configuration space,</p>
<div class="math-display">$$\frac{d}{d\beta}\mathbb E_\beta[f]=\sum_{e\in E_+}c_\beta(e)\operatorname{Cov}_\beta(f,X_e),\qquad c_\beta(e)=\frac{J_e}{1-e^{-\beta J_e}}.$$</div>
<p>For $e\in E_+$ the coefficients satisfy</p>
<div class="math-display">$$c_\beta(e)\geq\frac1\beta,\qquad 0&lt;\frac{J_e}{e^{\beta J_e}-1}=e^{-\beta J_e}c_\beta(e)\leq c_\beta(e).$$</div>
<p><em>Proof.</em> The finite-profile formula <a href="/tag/7WIO/">7WIO</a> gives the summand $J_e e^{-\beta J_e}\mathbb E_\beta[\Delta_e f]$. For positive $J_e$, substitute the coordinate covariance identity and cancel $q_\beta(e)(1-q_\beta(e))$. A zero-weight coordinate is deterministically closed and contributes zero to the derivative and to the covariance; it is omitted rather than assigned the undefined quotient $0/0$. Finally, $1-e^{-\beta J_e}\leq\beta J_e$ gives the first coefficient bound, and multiplying numerator and denominator by $e^{\beta J_e}$ gives the second.</p>
<p>For increasing $f$, every covariance is nonnegative. Replacing $c_\beta(e)$ by the smaller coefficient therefore gives a lower bound on the derivative. It is not a two-sided comparison uniform in the weights: for fixed $\beta&gt;0$, the ratio of the smaller coefficient to the exact one is $e^{-\beta J_e}$, which tends to zero as $J_e\to\infty$.</p>
<p>The restriction $\beta&gt;0$ matters. At $\beta=0$ all coordinate covariances vanish, yet for one edge with weight $J&gt;0$ and $A=\{X_e=1\}$ the right derivative of $\mathbb P_\beta(A)$ is $J$. The endpoint formula is the increment or closed-pivotal formula <a href="/tag/IENL/">IENL</a>, not substitution into a singular covariance coefficient.</p>

## From a covariance bound to a derivative {#section-revealment}

<a id="tag-8IGH" data-assertion="proposition" data-title="Conditional revealment-to-derivative conversion"></a>
<p>Fix $\beta&gt;0$ in the preceding finite intensity model, and let $A$ be increasing. Suppose numbers $C\geq0$ and $0\leq\delta_e\leq1$ satisfy the explicit input inequality</p>
<div class="math-display">$$C\leq\sum_{e\in E}\delta_e\operatorname{Cov}_\beta(\mathbf1_A,X_e).$$</div>
<p>Write $F(\beta)=\mathbb P_\beta(A)$ and define</p>
<div class="math-display">$$R=\max_{e\in E_+}\frac{\delta_e}{c_\beta(e)},$$</div>
<p>with maximum zero when $E_+$ is empty. If $R&gt;0$, then $F'(\beta)\geq C/R$. If $R=0$, then $C=0$. In particular, if $0&lt;D\leq1$ and $\delta_e\leq D$ for every $e\in E_+$, then</p>
<div class="math-display">$$F'(\beta)\geq\frac{C}{\beta D}.$$</div>
<p><em>Proof.</em> Zero-weight coordinates have zero covariance, and all remaining covariances are nonnegative. Hence</p>
<div class="math-display">$$C\leq\sum_{e\in E_+}\delta_e\operatorname{Cov}_\beta(\mathbf1_A,X_e)\leq R\sum_{e\in E_+}c_\beta(e)\operatorname{Cov}_\beta(\mathbf1_A,X_e)=RF'(\beta).$$</div>
<p>This proves both alternatives for $R$. Since $c_\beta(e)\geq1/\beta$, the bound $\delta_e\leq D$ also gives $C\leq\beta D F'(\beta)$ directly, including the case $R=0$.</p>
<p>The numbers $\delta_e$ may be revealment probabilities of a decision tree, but the displayed input inequality must first be established for that tree and the events in question. No decision-tree theorem is assumed merely by naming these numbers revealments. Nor is an infinite-volume derivative obtained by this finite-coordinate argument.</p>

## Source scope {#section-source}

<p>The covariance identity and coefficient discussion make precise the finite-coordinate calculation in the preliminary notes, Chapter 6, lines 2634–2643. The adjacent proposition S017 is not used here. As recorded in the project's source audit (N-ERR-05), its printed statement omits a necessary restriction: for a fair bit, taking both events to be $\{X=0\}$ makes their covariance $1/4$, whereas the covariance with $X$ is $-1/4$ and a tree deciding the event reveals the bit with probability one. The stated inequality would read $1/4\leq-1/4$.</p>
<p>A corrected OSSS theorem and the passage from finite decision trees to the infinite cluster and ghost-field applications require separate statements and proofs. This article supplies the algebraic conversion once the appropriate covariance bound is available.</p>

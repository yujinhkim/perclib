---
{
  "id": "russo-formula",
  "title": "Russo's formula",
  "subtitle": "Derivatives, coordinate increments and pivotal events",
  "kind": "theorem",
  "category": "Foundations",
  "summary": "Differentiate a finite product law without dividing by coordinate probabilities, keeping endpoint derivatives and closed pivotality explicit.",
  "context": [
    "A finite coordinate set $E$ and configurations $\\omega\\subseteq E$.",
    "A product Bernoulli profile $q\\in[0,1]^E$; differentiable real extensions are used to discuss boundary parameters.",
    "Observables do not vary with the parameter. Pivotal-probability formulas require increasing events; signed forced-difference formulas do not."
  ],
  "related": [
    "product-model",
    "harris-inequality",
    "cutoff-families",
    "sharpness"
  ],
  "sourceIds": [
    "notes",
    "mathlib",
    "perclib-finite-polynomial",
    "perclib-cylinder-russo",
    "perclib-finite-russo"
  ],
  "aliases": [
    "Russo",
    "pivotal edge",
    "closed pivotal",
    "influence",
    "profile derivative",
    "intensity derivative"
  ],
  "prototypeUses": [
    "product-model"
  ]
}
---

## Coordinate increments and pivotality {#section-pivotality}

<a id="tag-71GK" data-assertion="definition" data-title="Forced configurations, coordinate increments and pivotality"></a><p>Let $E$ be a finite set of coordinates and identify a configuration with its open set $\omega\subseteq E$. Write $\omega^{e,1}=\omega\cup\{e\}$ and $\omega^{e,0}=\omega\setminus\{e\}$. For $f:\{0,1\}^E\to\mathbb R$, set</p><div class="math-display">$$\Delta_e f(\omega)=f(\omega^{e,1})-f(\omega^{e,0}).$$</div><p>The increment does not depend on the current state of $e$. For an increasing event $A$, call $e$ pivotal when $\omega^{e,1}\in A$ and $\omega^{e,0}\notin A$. Then $\Delta_e\mathbf1_A$ is exactly the pivotal indicator. The <em>closed-pivotal</em> event requires in addition that $e\notin\omega$; these are different events.</p><p>All functions and events on this finite configuration space are measurable. No monotonicity assumption is needed for the observable version of Russo's formula; increasingness is used when replacing a signed increment by a pivotal indicator.</p>

## Differentiating a finite product law {#section-profile}

<a id="tag-7WIO" data-assertion="theorem" data-title="Finite-profile Russo formula for observables"></a><p>For a real profile $q\in\mathbb R^E$, define the polynomial</p><div class="math-display">$$\Phi_f(q)=\sum_{\omega\subseteq E} f(\omega)\prod_{e\in\omega}q_e\prod_{e\notin\omega}(1-q_e).$$</div><p>When $q\in[0,1]^E$, this is $\mathbb E_q[f]$. If each real-valued coordinate $q_e(t)$ is differentiable at $t_0$, then</p><div class="math-display">$$\left.\frac{d}{dt}\Phi_f(q(t))\right|_{t=t_0}=\sum_{e\in E}q'_e(t_0)\,\Phi_{\Delta_e f}(q(t_0)).$$</div><p>This polynomial identity holds even when some coordinates equal zero or one; outside the cube it remains an algebraic identity, not a probability statement.</p><p><em>Proof.</em> Fix $e$ and pair each configuration not containing $e$ with the configuration obtained by opening $e$. If $\eta\subseteq E\setminus\{e\}$ and $w_q^{(-e)}(\eta)$ denotes its product weight on the other coordinates, then</p><div class="math-display">$$\Phi_f(q)=\sum_{\eta\subseteq E\setminus\{e\}}\bigl[q_e f(\eta\cup\{e\})+(1-q_e)f(\eta)\bigr]w_q^{(-e)}(\eta).$$</div><p>Differentiating in $q_e$ gives the weighted sum of $f(\eta\cup\{e\})-f(\eta)$. Since $\Delta_e f$ ignores coordinate $e$, summing its full product weights contributes the factor $q_e+(1-q_e)=1$. Hence $\partial_e\Phi_f=\Phi_{\Delta_e f}$, and the ordinary chain rule gives the result. Every sum is finite, and no coordinate probability has been divided out.</p><p>For a probability family specified only on a parameter set $D$, let $t_0\in D$ be an accumulation point of $D$ and suppose differentiable real extensions $q_e$ agree with that family on $D$ and at $t_0$. The expectation on $D$ then agrees with $\Phi_f(q(t))$, so the same expression is its derivative along $D$ at $t_0$. At an endpoint of an interval, this gives the appropriate one-sided derivative. The polynomial extension need not take values in the probability cube outside $D$.</p>

<p>For completeness, the pairing can be expressed directly in the weights. Write $\sigma_e(\omega)=1$ when $e$ is open and $-1$ when it is closed, and let $w_q^{(-e)}(\omega)$ omit the factor at $e$. Then</p>
<div class="math-display">$$\partial_e w_q(\omega)=\sigma_e(\omega)w_q^{(-e)}(\omega),\qquad
\sum_\omega f(\omega)\sigma_e(\omega)w_q^{(-e)}(\omega)=\Phi_{\Delta_e f}(q).$$</div>
<p>Flipping $e$ is an involution, preserves the deleted weight and interchanges the two signs. The forced increment is unchanged by flipping or forcing $e$. Pairing the two terms therefore gives the second identity, including at endpoint profiles. Identifying binary functions with their open sets turns forcing into insertion or deletion of $e$ and the finite sum into the canonical product integral. This uses no second probability law.</p>
<p>Substituting $q_e(\beta)=1-e^{-\beta J_e}$ into the polynomial derivative gives</p>
<div class="math-display">$$\frac{d}{d\beta}\Phi_f(q(\beta))=\sum_e J_e e^{-\beta J_e}\Phi_{\Delta_e f}(q(\beta))$$</div>
<p>for every real $J_e$ and real $\beta$. Outside parameter sets where all $q_e$ lie in $[0,1]$, this is only a polynomial-composed-with-exponentials identity. For an increasing event, the same algebra replaces its forced increment by its pivotal indicator even there, but its weighted sum need not be a probability. With no coordinates the sum is empty and the derivative is zero. A one-coordinate open indicator has polynomial expectation $q_e$, so its homogeneous derivative is one and its intensity derivative at zero is $J_e$, without any endpoint division.</p>

## Increasing events and homogeneous parameters {#section-events}

<a id="tag-WU9R" data-assertion="corollary" data-title="Finite-profile Russo formula for increasing events"></a><p>Under the differentiability assumptions above, if $A$ is increasing and $q(t_0)\in[0,1]^E$, then</p><div class="math-display">$$\left.\frac{d}{dt}\Phi_{\mathbf1_A}(q(t))\right|_{t=t_0}=\sum_{e\in E}q'_e(t_0)\,\mathbb P_{q(t_0)}(e\text{ is pivotal for }A).$$</div><p>This follows by substituting $f=\mathbf1_A$. It is also the derivative of the event probability on any parameter domain on which $q(t)$ is a probability profile. The derivatives $q'_e(t_0)$ may have either sign.</p><a id="tag-4IHK" data-assertion="corollary" data-title="Homogeneous Russo formula including endpoint derivatives"></a><p>For the homogeneous family $q_e=p$,</p><div class="math-display">$$\frac{d}{dp}\mathbb P_p(A)=\sum_{e\in E}\mathbb P_p(e\text{ is pivotal for }A),\qquad 0&lt;p&lt;1.$$</div><p>The same right-hand side gives the right derivative at $p=0$ and the left derivative at $p=1$. These are also the ordinary derivatives of the real polynomial extension. For the single-coordinate event $A=\{e\text{ open}\}$, pivotality occurs for every configuration, so the derivative is one, including at both endpoints. A formula that conditions on a positive-probability open or closed state would obscure precisely these boundary cases.</p>

## Intensity parameters and closed pivotality {#section-intensity}

<a id="tag-IENL" data-assertion="corollary" data-title="Intensity Russo formula and closed-pivotal form"></a><p>Let $J_e\geq0$ be finite and put $q_\beta(e)=1-e^{-\beta J_e}$ for finite $\beta\geq0$. For an increasing event $A$ depending on these finitely many coordinates,</p><div class="math-display">$$\frac{d}{d\beta}\mathbb P_\beta(A)=\sum_{e\in E}J_e e^{-\beta J_e}\,\mathbb P_\beta(e\text{ is pivotal for }A)=\sum_{e\in E}J_e\,\mathbb P_\beta(e\text{ is closed pivotal for }A).$$</div><p>At $\beta=0$ the probability derivative is taken from the right. The first equality follows from $q'_\beta(e)=J_e e^{-\beta J_e}$. For the second, pivotality depends only on the other coordinates and is therefore independent of the state of $e$, giving</p><div class="math-display">$$\mathbb P_\beta(e\text{ is closed pivotal})=(1-q_\beta(e))\mathbb P_\beta(e\text{ is pivotal})=e^{-\beta J_e}\mathbb P_\beta(e\text{ is pivotal}).$$</div><p>Thus the exponential factor may be absorbed into <em>closed</em> pivotality, but it must not be discarded while retaining the state-independent pivotal event.</p><p>For an arbitrary real observable on the same finite space, the same independence yields the form used in the notes:</p><div class="math-display">$$\frac{d}{d\beta}\mathbb E_\beta[f]=\sum_{e\in E}J_e\,\mathbb E_\beta\bigl[f(\omega\cup\{e\})-f(\omega)\bigr].$$</div><p>Indeed, the difference in this expectation is $\mathbf1_{\{e\text{ closed}\}}\Delta_e f$, whose expectation is $(1-q_\beta(e))\mathbb E_\beta[\Delta_e f]$. This explains why the notes' intensity formula and the profile derivative have different-looking coefficients.</p>

## Cylinder events in an arbitrary ambient product {#section-cylinder}

<a id="tag-XU3W" data-assertion="theorem" data-title="Finite-cylinder Russo with signed forced differences and arbitrary ambient coordinates"></a>
<p>Let $I$ be any index set, let $F\subseteq I$ be finite, and let $A=\{\omega:\omega\cap F\in\mathcal B\}$ for some $\mathcal B\subseteq2^F$. Let $p(t)\in[0,1]^I$ be a probability profile on a parameter domain $D$, with $t_0\in D$ an accumulation point of $D$. For each $e\in F$, suppose a real function $q_e$ is differentiable at $t_0$ and agrees with $p_e$ on $D$. Then the derivative along $D$ is</p>
<div class="math-display">$$\left.\frac{d}{dt}\mathbb P_{p(t)}(A)\right|_{t=t_0,\ t\in D}=\sum_{e\in F}q'_e(t_0)\left[\mathbb P_{p(t_0)}(\omega\cup\{e\}\in A)-\mathbb P_{p(t_0)}(\omega\setminus\{e\}\in A)\right].$$</div>
<p>No regularity is assumed for coordinates outside $F$, and their forced differences vanish. If $A$ is increasing, each bracket equals the probability that forcing $e$ open makes $A$ hold and forcing it closed makes $A$ fail. More generally, this bracket-to-pivotal identity holds for every increasing measurable event on $2^I$, even without finite dependence; only the derivative formula requires the cylinder assumption here.</p>
<p><em>Proof.</em> By the <a href="/tag/ZNMQ/">finite restriction law</a>, the event probability is the finite polynomial for $\mathbf1_{\mathcal B}$ evaluated at $p|_F$. On $D$ it agrees with the same polynomial evaluated at the differentiable real extensions. Apply <a href="/tag/7WIO/">7WIO</a> and identify the expected indicator increment with the displayed difference of probabilities. Restriction commutes with inserting or removing a coordinate of $F$. For $e\notin F$, neither operation changes $\omega\cap F$, proving the vanishing claim.</p>
<p>For any increasing measurable event, the forced-closed event is contained in the forced-open event. Both are measurable because the coordinate-forcing maps are measurable. Subtracting their finite probabilities gives the probability of their difference, exactly the state-independent pivotal event. This argument uses neither countability nor division by a coordinate probability.</p>
<p>For finite nonnegative $J_e$ and $p_e(\beta)=1-e^{-\beta J_e}$ on $F$, take $D=[0,\infty)$ and $q'_e(\beta)=J_e e^{-\beta J_e}$. The signed formula applies to any cylinder event, including at zero with a right derivative. Outside $F$, the profile may vary arbitrarily with $\beta$. In the increasing case this gives the pivotal form; the closed-pivotal conversion is the one in <a href="/tag/IENL/">IENL</a>.</p>
<p>An empty block gives a constant event probability and an empty derivative sum. For a decreasing single-coordinate event, the bracket is $-1$, so its derivative is $-q'_e(t_0)$; replacing signed differences by positive pivotal probabilities would be wrong. The point of the real extensions is only to differentiate the finite polynomial. They need not be probability profiles away from $D$.</p>

## Finite dependence and infinite volume {#section-scope}

<p>The formulas also apply to a cylinder observable in an infinite product space: choose a finite set of coordinates on which it depends and integrate out the rest. They do not by themselves apply to an arbitrary infinite-volume event. Limits of event probabilities need not permit differentiation under the limit, and a formal infinite pivotal sum still needs a convergence argument.</p><p>For the <a href="#/cutoff-families">integrated cutoff family</a>, the already recorded finite-edge identity is the profile formula with its actual derivative $q'_{\beta,r}(e)$. Corners in the cutoff parameter require one-sided or almost-everywhere statements. Replacing that family by a hard truncation, or differentiating an infinite-volume probability merely because it is monotone, would require a different argument.</p>

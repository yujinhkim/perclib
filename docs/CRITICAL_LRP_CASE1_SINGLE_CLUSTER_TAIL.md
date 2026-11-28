# The Case-1 single-cluster tail, proved from finite first moments

`Analysis/SecondMomentCase1/Capstone` proves the displayed tail used by the
Case-1 proof of Corollary I.4.14 at the actual cutoff law:
$$P_{\beta_c,r}(|K|\ge n)\le\sqrt{2m/n}\exp\{-n/(4m^2)\},\qquad n\ge1,$$
where $m=(E_{\beta_c,r}|K|)_{\mathrm{toReal}}$.
The only remaining hypothesis in `singleClusterTail_cutMoment_one` is
`M.cutMoment 1 r ≠ ⊤`.

The proof applies Markov at an order depending on $u=n/m^2$ to the production
ordinary tree-moment inequality
$$E|K|^q\le(2q-3)!!\,m^{2q-1}.$$
The odd-double-factorial bridge to `VolumeMoments.M` is proved. The scale cases
are a direct probability bound when $n/m<1$, order one for $u\le1$ with
$n/m\ge1$, order two for $1\le u\le6$, order five for $6<u\le16$, and order
$\lfloor u/2\rfloor$ for $u>16$. For the last case, a factorial/Stirling bound
and $e^2u\le4e^{u/4}$ provide the required exponential slack. These arguments
do not use the unresolved mixed sixth moment or a bogus uniform critical mean.

`cutLaw_tail_le_markov` gives the corresponding real-valued Markov estimate
at the actual law, with finite thresholds and explicit conversions between
`ENNReal` and real quantities. `mr_le_cutMoment_one_finite` and
`hydro_of_cutMoment_one_finite` then discharge both the `1 ≤ m` and
`SingleClusterTail` premises of the earlier wrappers. Finiteness of the mean is
still required throughout; the root's membership in its cluster supplies
$m\ge1$, not finiteness.

`hydro_of_firstMoment_asymptotic` additionally derives that finiteness from the
sharp first-moment asymptotic `hP`, exactly as in the existing source modules,
through `cutMassAt_zero_eq_cutMoment`. It therefore gives Case-1 `Hydro` from
$3\alpha<d$ and $\chi\sim c r^\alpha$ with $c>0$. **That first-moment growth or
asymptotic remains an input.** Nothing here proves it, sharpness, the sixth
mixed moment, other cases, or unconditional canonical `Hydro`.

The older `TailScale` file is now a compatibility re-export of this completed
proof, retaining its only separately named even-product helper. The older
scale notes are historical descriptions of the partial precursor, not open
obligations of this completed result.

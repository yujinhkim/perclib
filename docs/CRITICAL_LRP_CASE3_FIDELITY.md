# Independent source-fidelity review: Case 3 and Lemma I.4.3

The independent Ultramath review `smwu5k11q/m1` was accepted after coordinator checking of its
source comparison, threshold calculations, statement extracts, and import-separation test. Its full
report is retained at `.ultramath/smwu5k11q/m1/AUDIT.md`. The target was HEAD `4f858d4`.

## Verdict and scope

No mathematical or source-fidelity discrepancy was found in the literal printed Case 3 transport
or the joint Lemma I.4.3 wrapper. The review classified the source premises against the exact Lean
statements and expanded the meaning-carrying definitions rather than relying on names, docstrings,
or axiom counts.

* `HD_of_HD3` identifies the raw, unshifted third disjunct of `Orchestration.HD` by a proof term.
* `Case23.isLogErrorFunction_nablaTail_of_HD_case2_or_case3` takes exactly HD(2) or HD(3), not the
  whole HD disjunction; Case 1 is excluded.
* `M.nablaTail` is the closed radial supremum of the literal uncut open triangle at `betaCrit`,
  evaluated at the actual normalized `M.S.dist`, not the sup-norm tail.
* The stated `IsLogErrorFunction` includes the paper's logarithmic integrability, measurability,
  and unbounded-tail integral. It additionally proves convergence to zero, which the paper records
  separately. No finiteness or norm-equivalence premise is hidden; finite open triangles are proved
  before using `toReal`.
* The `α = 2` conjunct is inert in the stronger Case 3 implication. Keeping it in the printed
  disjunct is faithful, and dropping it in the stronger intermediate theorem is a valid extension.

## The crucial applicability caveat

The row in `CRITICAL_LRP_COVERAGE.md` is FULL **for the paper's printed conditional**. It does not
say that the intended models satisfy printed HD(3). Independently of whether any particular model
can satisfy it, the Lean proof establishes the raw hypothesis's rigidity:

* nonzero displacement with source norm below one is forbidden, because the unshifted inverse log
  would make a nonnegative two-point probability lie below a negative right side;
* on the unit source shell, Lean's `(log 1)⁻¹ = 0` forces the two-point probability to vanish.

Therefore a model with positive two-point connectivity at normalized distance below one directly
contradicts printed HD(3). This raises a source-level applicability concern for intended models;
it is not silently erased or counted as model non-vacuity. The separately proved theorem in
`Case3SourceNorm` uses the shifted `log (1 + ρ)` input when that bound is available. That theorem
is a different predicate and is not in the import cone of the literal `Case23` wrapper.

## Checks

The raw and shifted integration gates at `aa49a12` and `4f858d4` passed with only the standard
axioms, and the raw production packet's 37 axiom reports were independently rebuilt. The audit's
statement extracts rechecked the direct wrapper, its `HD3` input, the definition of the source tail,
and the standard axiom basis. The import test confirmed that all three shifted names are unknown
when only `Case23` is imported.

For the scratch checks, the coordinator corrected module headers and the qualification of
`SourceModelData.logRadialBound_of_toReal_le`. These helper-file corrections changed no production
statement. The audit also observed that the rigidity fact `hρ1` is not needed by the transport
calculation and that one narrative declaration name was stale; the latter has been corrected in the
module header. Neither point affects the mathematical result.

Compilation and axiom cleanliness remain only proof-status evidence. The FULL classification above
comes from the separate statement-to-source audit, with the printed-hypothesis limitation retained.

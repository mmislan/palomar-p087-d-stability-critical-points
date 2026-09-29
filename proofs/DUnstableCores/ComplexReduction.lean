module

public import proofs.DUnstableCores.PositiveRealChild

@[expose] public section

/-!
# Reduction to the genuinely complex instability wall

The positive-real endpoint can be contraposed at the coefficient level.  If
every supported child is D-non-unstable, no coefficient in the characteristic
polynomial of the source Jacobian can be negative, and a positive real
eigenpair is impossible.
-/

namespace DUnstableCores

/-- No D-unstable supported child forces coefficientwise nonnegativity of the
source characteristic polynomial. -/
theorem dNonUnstable_children_imply_charpoly_coeff_nonneg
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    [Fintype Reaction] [DecidableEq Reaction]
    (Q : SourceNetwork Species Reaction) (R : Reactivity Q)
    (hchildren : ∀ child : ChildSelection Q,
      DNonUnstable child.realMatrix) :
    ∀ k : ℕ, 0 ≤ (Q.jacobian R).charpoly.coeff k := by
  intro k
  by_contra hnonneg
  have hk : (Q.jacobian R).charpoly.coeff k < 0 := lt_of_not_ge hnonneg
  obtain ⟨child, hchild⟩ :=
    negative_charpoly_coefficient_yields_dUnstable_child Q R hk
  exact ((not_dNonUnstable_iff_dUnstable child.realMatrix).mpr hchild)
    (hchildren child)

/-- Under the same no-D-core hypothesis, the Jacobian cannot have a positive
real eigenpair. -/
theorem dNonUnstable_children_exclude_positiveRealEigenpair
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    [Fintype Reaction] [DecidableEq Reaction]
    (Q : SourceNetwork Species Reaction) (R : Reactivity Q)
    (hchildren : ∀ child : ChildSelection Q,
      DNonUnstable child.realMatrix) :
    ¬ HasPositiveRealEigenpair (Q.jacobian R) := by
  intro hpositive
  obtain ⟨child, hchild⟩ :=
    positiveRealEigenpair_yields_dUnstable_child Q R hpositive
  exact ((not_dNonUnstable_iff_dUnstable child.realMatrix).mpr hchild)
    (hchildren child)

/-- A complex eigenpair of a real matrix whose eigenvalue is real yields a
real eigenpair.  Either the real or imaginary part of the complex eigenvector
is a nonzero real eigenvector. -/
theorem positiveRealEigenpair_of_complex_eigenpair_im_zero
    {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℝ} {lam : ℂ} {v : ι → ℂ}
    (hlam : 0 < lam.re) (him : lam.im = 0)
    (heig : HasEigenpair A lam v) :
    HasPositiveRealEigenpair A := by
  let vr : ι → ℝ := fun i => (v i).re
  let vi : ι → ℝ := fun i => (v i).im
  have hreig : ∀ i, Matrix.mulVec A vr i = lam.re * vr i := by
    intro i
    have hi := congrArg Complex.re (heig.2 i)
    simpa [Matrix.mulVec, dotProduct, complexify, vr, him] using hi
  have hiig : ∀ i, Matrix.mulVec A vi i = lam.re * vi i := by
    intro i
    have hi := congrArg Complex.im (heig.2 i)
    simpa [Matrix.mulVec, dotProduct, complexify, vi, him] using hi
  by_cases hvr : vr ≠ 0
  · exact ⟨lam.re, vr, hlam, hvr, hreig⟩
  · have hvrzero : vr = 0 := not_ne_iff.mp hvr
    have hvi : vi ≠ 0 := by
      intro hvizero
      apply heig.1
      funext i
      apply Complex.ext
      · simpa [vr] using congrFun hvrzero i
      · simpa [vi] using congrFun hvizero i
    exact ⟨lam.re, vi, hlam, hvi, hiig⟩

/-- Once positive-real instability has been excluded, every right-half-plane
eigenpair witness is genuinely nonreal. -/
theorem hurwitzUnstable_has_nonreal_witness_of_no_positiveRealEigenpair
    {ι : Type*} [Fintype ι] {A : Matrix ι ι ℝ}
    (hunstable : HurwitzUnstable A)
    (hno : ¬ HasPositiveRealEigenpair A) :
    ∃ lam : ℂ, ∃ v : ι → ℂ,
      0 < lam.re ∧ HasEigenpair A lam v ∧ lam.im ≠ 0 := by
  obtain ⟨lam, v, hlam, heig⟩ := hunstable
  refine ⟨lam, v, hlam, heig, ?_⟩
  intro him
  exact hno (positiveRealEigenpair_of_complex_eigenpair_im_zero hlam him heig)

/-- Exact complex-wall reduction for a source Jacobian with no D-unstable
supported child. -/
theorem noDUnstableChild_hurwitzUnstable_has_nonreal_witness
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    [Fintype Reaction] [DecidableEq Reaction]
    (Q : SourceNetwork Species Reaction) (R : Reactivity Q)
    (hchildren : ∀ child : ChildSelection Q,
      DNonUnstable child.realMatrix)
    (hunstable : HurwitzUnstable (Q.jacobian R)) :
    ∃ lam : ℂ, ∃ v : Species → ℂ,
      0 < lam.re ∧ HasEigenpair (Q.jacobian R) lam v ∧ lam.im ≠ 0 :=
  hurwitzUnstable_has_nonreal_witness_of_no_positiveRealEigenpair hunstable
    (dNonUnstable_children_exclude_positiveRealEigenpair Q R hchildren)

end DUnstableCores

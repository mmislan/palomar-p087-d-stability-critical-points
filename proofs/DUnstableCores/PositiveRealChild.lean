module

public import proofs.DUnstableCores.SupportedWeightNormalization

@[expose] public section

/-!
# Closing the positive-real branch

A negative determinant of `-A` is a negative constant coefficient of the
monic characteristic polynomial.  Continuity and eventual positivity yield a
strictly positive real root, hence a positive eigenpair.
-/

namespace DUnstableCores

open Polynomial

theorem det_neg_eq_charpoly_coeff_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) :
    Matrix.det (-A) = A.charpoly.coeff 0 := by
  rw [Matrix.det_neg, Matrix.det_eq_sign_charpoly_coeff]
  have hsquare : ((-1 : ℝ) ^ Fintype.card ι) ^ 2 = 1 := by
    rw [← pow_mul]
    simp
  have hmul : (-1 : ℝ) ^ Fintype.card ι *
      (-1 : ℝ) ^ Fintype.card ι = 1 := by
    simpa [pow_two] using hsquare
  rw [← mul_assoc, hmul, one_mul]

theorem monic_negative_constant_has_positive_root
    (p : ℝ[X]) (hmonic : p.Monic) (hconstant : p.coeff 0 < 0) :
    ∃ x : ℝ, 0 < x ∧ p.IsRoot x := by
  by_contra hnone
  push Not at hnone
  have hroots : ∀ y : ℝ, p.IsRoot y → y < 0 := by
    intro y hy
    have hynonpos : y ≤ 0 := le_of_not_gt fun hypos => hnone y hypos hy
    have hyne : y ≠ 0 := by
      intro hyzero
      subst y
      apply hconstant.ne
      rw [coeff_zero_eq_eval_zero]
      exact hy
    exact lt_of_le_of_ne hynonpos hyne
  have hevalpos : 0 < p.eval 0 :=
    p.zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg
      hroots (by simp [hmonic.leadingCoeff])
  have hevalneg : p.eval 0 < 0 := by
    rw [← coeff_zero_eq_eval_zero]
    exact hconstant
  linarith

theorem charpoly_positive_root_implies_positiveRealEigenpair
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hroot : A.charpoly.IsRoot lam) : HasPositiveRealEigenpair A := by
  classical
  let f : Module.End ℝ (ι → ℝ) := A.mulVecLin
  have hrootEnd : f.charpoly.IsRoot lam := by
    simpa [f, Matrix.charpoly_mulVecLin] using hroot
  have heigenvalue : Module.End.HasEigenvalue f lam :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly f lam).mpr hrootEnd
  obtain ⟨v, hv⟩ := heigenvalue.exists_hasEigenvector
  refine ⟨lam, v, hlam, hv.2, ?_⟩
  intro i
  have happly : f v = lam • v := Module.End.mem_eigenspace_iff.mp hv.1
  have hi := congrFun happly i
  simpa [f, Matrix.mulVecLin_apply] using hi

theorem det_neg_negative_implies_dUnstable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hdet : Matrix.det (-A) < 0) : DUnstable A := by
  have hconstant : A.charpoly.coeff 0 < 0 := by
    rwa [← det_neg_eq_charpoly_coeff_zero A]
  obtain ⟨lam, hlam, hroot⟩ := monic_negative_constant_has_positive_root
    A.charpoly A.charpoly_monic hconstant
  exact hurwitzUnstable_implies_dUnstable A
    (hasPositiveRealEigenpair_implies_hurwitzUnstable
      (charpoly_positive_root_implies_positiveRealEigenpair hlam hroot))

/-- A single negative source characteristic coefficient already produces a
literal D-unstable supported child. -/
theorem negative_charpoly_coefficient_yields_dUnstable_child
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    [Fintype Reaction] [DecidableEq Reaction]
    (Q : SourceNetwork Species Reaction) (R : Reactivity Q) {k : ℕ}
    (hk : (Q.jacobian R).charpoly.coeff k < 0) :
    ∃ child : ChildSelection Q, DUnstable child.realMatrix := by
  obtain ⟨f, hf, hneg⟩ :=
    negative_charpoly_coefficient_localizes_to_supported_weight Q R hk
  let child := supportedAssignmentChild Q f hf
  have hactive : Matrix.det (activeNegativeMatrix Q f) < 0 :=
    negative_supported_weight_coefficient_implies_active_det_negative
      Q R f hf hneg
  have hchild : Matrix.det (-child.realMatrix) < 0 := by
    rw [← activeNegativeMatrix_eq_neg_child_realMatrix Q f hf]
    exact hactive
  exact ⟨child, det_neg_negative_implies_dUnstable child.realMatrix hchild⟩

/-- Exact positive-real localization into a literal D-unstable child. -/
theorem positiveRealEigenpair_yields_dUnstable_child
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    [Fintype Reaction] [DecidableEq Reaction]
    (Q : SourceNetwork Species Reaction) (R : Reactivity Q)
    (h : HasPositiveRealEigenpair (Q.jacobian R)) :
    ∃ child : ChildSelection Q, DUnstable child.realMatrix := by
  obtain ⟨k, hk⟩ := positiveRealEigenpair_has_negative_charpoly_coefficient h
  exact negative_charpoly_coefficient_yields_dUnstable_child Q R hk

/-- The complete positive-real branch: a positive real Jacobian eigenpair
produces a principal-minimal D-unstable source child-selection core. -/
theorem positiveRealEigenpair_yields_principal_minimal_core
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    [Fintype Reaction] [DecidableEq Reaction]
    (Q : SourceNetwork Species Reaction) (R : Reactivity Q)
    (h : HasPositiveRealEigenpair (Q.jacobian R)) :
    ∃ core : ChildSelection Q, IsDUnstableCore core := by
  obtain ⟨child, hchild⟩ :=
    positiveRealEigenpair_yields_dUnstable_child Q R h
  obtain ⟨core, hrestricts, hcore⟩ :=
    dUnstable_childSelection_contains_core child hchild
  exact ⟨core, hcore⟩

end DUnstableCores

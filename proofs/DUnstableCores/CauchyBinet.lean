module

public import proofs.DUnstableCores.CharPoly
public import proofs.DUnstableCores.Source

@[expose] public section

/-!
# Rectangular determinant expansion for source Jacobians

This is the exact algebraic kernel behind child-selection localization.  It
keeps reaction assignments explicit, so multiplicities and source support
cannot be lost by quotienting too early.
-/

namespace DUnstableCores

open scoped BigOperators

variable {α ρ : Type*}

/-- The square stoichiometric matrix selected by an assignment of one reaction
to each column/species. -/
def selectedMatrix {K : Type*} (S : Matrix α ρ K) (f : α → ρ) : Matrix α α K :=
  fun i j => S i (f j)

/-- Function-indexed Cauchy--Binet expansion.  Noninjective assignments remain
in the displayed sum here and are eliminated by the next theorem. -/
theorem det_rectangular_expansion {K : Type*} [CommRing K]
    [Fintype α] [Fintype ρ] [DecidableEq α]
    (S : Matrix α ρ K) (R : Matrix ρ α K) :
    Matrix.det (fun i j => ∑ r : ρ, S i r * R r j) =
      ∑ f : α → ρ, Matrix.det (selectedMatrix S f) * ∏ j, R (f j) j := by
  classical
  erw [Matrix.det_apply']
  simp_rw [Fintype.prod_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f hf
  rw [Matrix.det_apply', Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [Finset.prod_mul_distrib]
  simp only [selectedMatrix]
  ring

theorem selectedMatrix_det_eq_zero_of_not_injective
    {K : Type*} [CommRing K] [Fintype α] [DecidableEq α]
    (S : Matrix α ρ K) (f : α → ρ) (hf : ¬Function.Injective f) :
    Matrix.det (selectedMatrix S f) = 0 := by
  classical
  obtain ⟨i, j, hfij, hij⟩ := Function.not_injective_iff.mp hf
  apply Matrix.det_zero_of_column_eq hij
  intro k
  simp [selectedMatrix, hfij]

/-- Exact source-valid full-size child-assignment predicate. -/
def SupportedAssignment {Species Reaction : Type*}
    (Q : SourceNetwork Species Reaction) (f : Species → Reaction) : Prop :=
  Function.Injective f ∧ ∀ s, Q.Reactant s (f s)

/-- Exact summand with classical support filtering hidden behind a stable
definition, rather than exposed as an extra theorem parameter. -/
noncomputable def supportedAssignmentWeight
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    (Q : SourceNetwork Species Reaction) (R : Reactivity Q)
    (f : Species → Reaction) : ℝ := by
  classical
  exact if SupportedAssignment Q f then
    Matrix.det (selectedMatrix (fun i r => (Q.stoich i r : ℝ)) f) *
      ∏ j, R.value (f j) j
  else 0

/-- Unsupported assignments have zero exact Cauchy--Binet weight. -/
theorem unsupported_assignment_weight_zero
    {Species Reaction : Type*} [Fintype Species] [Fintype Reaction]
    [DecidableEq Species]
    (Q : SourceNetwork Species Reaction) (R : Reactivity Q)
    (f : Species → Reaction) (hf : ¬ SupportedAssignment Q f) :
    Matrix.det (selectedMatrix (fun i r => (Q.stoich i r : ℝ)) f) *
        ∏ j, R.value (f j) j = 0 := by
  classical
  by_cases hinj : Function.Injective f
  · have hsupport : ¬∀ s, Q.Reactant s (f s) := by
      intro hs
      exact hf ⟨hinj, hs⟩
    obtain ⟨s, hs⟩ := not_forall.mp hsupport
    have hz : R.value (f s) s = 0 := R.zero_of_not_reactant (f s) s hs
    have hprod : (∏ j, R.value (f j) j) = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ s) hz
    rw [hprod, mul_zero]
  · erw [selectedMatrix_det_eq_zero_of_not_injective _ f hinj, zero_mul]

/-- The determinant of a source Jacobian is exactly the sum of the weights of
source-supported injective full child assignments. -/
theorem source_jacobian_det_child_assignment_sum
    {Species Reaction : Type*} [Fintype Species] [Fintype Reaction]
    [DecidableEq Species]
    (Q : SourceNetwork Species Reaction) (R : Reactivity Q) :
    Matrix.det (Q.jacobian R) =
      ∑ f : Species → Reaction, supportedAssignmentWeight Q R f := by
  classical
  change Matrix.det (fun i j => ∑ r : Reaction,
      (Q.stoich i r : ℝ) * R.value r j) = _
  rw [det_rectangular_expansion
    (S := fun i r => (Q.stoich i r : ℝ)) (R := R.value)]
  apply Finset.sum_congr rfl
  intro f hf
  by_cases hs : SupportedAssignment Q f
  · rw [supportedAssignmentWeight]
    simp only [hs, ↓reduceIte]
  · rw [unsupported_assignment_weight_zero Q R f hs,
      supportedAssignmentWeight]
    simp only [hs, ↓reduceIte]

end DUnstableCores

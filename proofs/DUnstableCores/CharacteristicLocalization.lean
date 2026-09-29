module

public import proofs.DUnstableCores.CauchyBinet

@[expose] public section

/-!
# Characteristic-coefficient localization by augmented child assignments

Identity columns encode powers of `X`; source columns encode reaction choices.
This converts the entire characteristic polynomial into one exact rectangular
Cauchy--Binet expansion without losing partial-selection multiplicities.
-/

namespace DUnstableCores

open scoped BigOperators
open Polynomial

variable {Species Reaction : Type*}

/-- Augmented characteristic source: identity columns carry `X`, while
reaction columns carry negative stoichiometry. -/
noncomputable def characteristicSource [DecidableEq Species]
    (Q : SourceNetwork Species Reaction) :
    Matrix Species (Species ⊕ Reaction) ℝ[X] :=
  fun i q => match q with
    | Sum.inl s => if i = s then X else 0
    | Sum.inr r => -C (Q.stoich i r : ℝ)

/-- Augmented characteristic response: identity columns select only their own
species, while reaction rows contain the exact reactivities. -/
noncomputable def characteristicResponse [DecidableEq Species]
    (Q : SourceNetwork Species Reaction)
    (R : Reactivity Q) : Matrix (Species ⊕ Reaction) Species ℝ[X] :=
  fun q j => match q with
    | Sum.inl s => if s = j then 1 else 0
    | Sum.inr r => C (R.value r j)

theorem characteristicSource_mul_response
    [Fintype Species] [Fintype Reaction] [DecidableEq Species]
    (Q : SourceNetwork Species Reaction) (R : Reactivity Q) :
    (fun i j => ∑ q : Species ⊕ Reaction,
      characteristicSource Q i q * characteristicResponse Q R q j) =
        Matrix.charmatrix (Q.jacobian R) := by
  ext i j
  rw [Fintype.sum_sum_type]
  simp [characteristicSource, characteristicResponse, Matrix.charmatrix,
    Matrix.scalar_apply, Matrix.diagonal_apply, SourceNetwork.jacobian,
    map_sum, eq_comm, sub_eq_add_neg]

/-- Exact full characteristic-polynomial expansion over augmented assignments. -/
theorem source_charpoly_augmented_expansion
    [Fintype Species] [Fintype Reaction] [DecidableEq Species]
    (Q : SourceNetwork Species Reaction) (R : Reactivity Q) :
    (Q.jacobian R).charpoly =
      ∑ f : Species → Species ⊕ Reaction,
        Matrix.det (selectedMatrix (characteristicSource Q) f) *
          ∏ j, characteristicResponse Q R (f j) j := by
  rw [Matrix.charpoly]
  rw [← det_rectangular_expansion (characteristicSource Q)
    (characteristicResponse Q R)]
  rw [characteristicSource_mul_response Q R]

/-- A supported augmented assignment is an injective partial child selection:
an identity choice must be the same species, and every reaction choice must
use an allowed source-reactant coordinate. -/
def SupportedCharacteristicAssignment (Q : SourceNetwork Species Reaction)
    (f : Species → Species ⊕ Reaction) : Prop :=
  Function.Injective f ∧ ∀ j, match f j with
    | Sum.inl s => s = j
    | Sum.inr r => Q.Reactant j r

theorem unsupported_characteristic_weight_zero
    [Fintype Species] [Fintype Reaction] [DecidableEq Species]
    (Q : SourceNetwork Species Reaction) (R : Reactivity Q)
    (f : Species → Species ⊕ Reaction)
    (hf : ¬ SupportedCharacteristicAssignment Q f) :
    Matrix.det (selectedMatrix (characteristicSource Q) f) *
        ∏ j, characteristicResponse Q R (f j) j = 0 := by
  classical
  by_cases hinj : Function.Injective f
  · have hsupport : ¬∀ j, match f j with
        | Sum.inl s => s = j
        | Sum.inr r => Q.Reactant j r := by
      intro hs
      exact hf ⟨hinj, hs⟩
    obtain ⟨j, hj⟩ := not_forall.mp hsupport
    have hz : characteristicResponse Q R (f j) j = 0 := by
      cases hfj : f j with
      | inl s =>
          simp [hfj, characteristicResponse] at hj ⊢
          exact hj
      | inr r =>
          simp [hfj] at hj
          simp [characteristicResponse,
            R.zero_of_not_reactant r j hj]
    have hprod : (∏ k, characteristicResponse Q R (f k) k) = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ j) hz
    rw [hprod, mul_zero]
  · rw [selectedMatrix_det_eq_zero_of_not_injective
      (characteristicSource Q) f hinj, zero_mul]

noncomputable def supportedCharacteristicWeight
    [Fintype Species] [Fintype Reaction] [DecidableEq Species]
    (Q : SourceNetwork Species Reaction) (R : Reactivity Q)
    (f : Species → Species ⊕ Reaction) : ℝ[X] := by
  classical
  exact if SupportedCharacteristicAssignment Q f then
    Matrix.det (selectedMatrix (characteristicSource Q) f) *
      ∏ j, characteristicResponse Q R (f j) j
  else 0

theorem source_charpoly_supported_assignment_sum
    [Fintype Species] [Fintype Reaction] [DecidableEq Species]
    (Q : SourceNetwork Species Reaction) (R : Reactivity Q) :
    (Q.jacobian R).charpoly =
      ∑ f : Species → Species ⊕ Reaction,
        supportedCharacteristicWeight Q R f := by
  classical
  rw [source_charpoly_augmented_expansion]
  apply Finset.sum_congr rfl
  intro f hf
  by_cases hs : SupportedCharacteristicAssignment Q f
  · rw [supportedCharacteristicWeight]
    simp only [hs, ↓reduceIte]
  · rw [unsupported_characteristic_weight_zero Q R f hs,
      supportedCharacteristicWeight]
    simp only [hs, ↓reduceIte]

/-- Every exact characteristic coefficient is therefore a finite sum of
source-supported partial child-assignment weights. -/
theorem source_charpoly_coefficient_supported_assignment_sum
    [Fintype Species] [Fintype Reaction] [DecidableEq Species]
    (Q : SourceNetwork Species Reaction) (R : Reactivity Q) (k : ℕ) :
    (Q.jacobian R).charpoly.coeff k =
      ∑ f : Species → Species ⊕ Reaction,
        (supportedCharacteristicWeight Q R f).coeff k := by
  have h := congrArg (fun p : ℝ[X] => p.coeff k)
    (source_charpoly_supported_assignment_sum Q R)
  simpa using h

end DUnstableCores

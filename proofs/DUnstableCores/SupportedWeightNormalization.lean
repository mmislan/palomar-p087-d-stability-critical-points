module

public import proofs.DUnstableCores.PositiveRealLocalization

@[expose] public section

/-!
# Normalization of a supported augmented weight

This file identifies the single monomial carried by a supported augmented
assignment.  Identity columns contribute `X`; reaction columns contribute the
negative selected stoichiometric column.
-/

namespace DUnstableCores

open scoped BigOperators
open Polynomial

/-- The constant matrix left after removing the `X` factor from every
inactive identity column. -/
noncomputable def assignmentNumericMatrix
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    (Q : SourceNetwork Species Reaction)
    (f : Species → Species ⊕ Reaction) : Matrix Species Species ℝ := by
  classical
  exact fun i j => match f j with
    | Sum.inl s => if i = s then 1 else 0
    | Sum.inr r => -(Q.stoich i r : ℝ)

/-- Diagonal factor contributed by an augmented column. -/
noncomputable def assignmentColumnFactor
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    (f : Species → Species ⊕ Reaction) (j : Species) : ℝ[X] := by
  classical
  exact if (f j).isRight then 1 else X

/-- Entrywise constant-polynomial lift, named so matrix multiplication is
elaborated in the matrix type before the function representation unfolds. -/
noncomputable def assignmentPolynomialMatrix
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    (Q : SourceNetwork Species Reaction)
    (f : Species → Species ⊕ Reaction) : Matrix Species Species ℝ[X] :=
  fun i j => C (assignmentNumericMatrix Q f i j)

theorem selected_characteristic_matrix_factorization
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    (Q : SourceNetwork Species Reaction)
    (f : Species → Species ⊕ Reaction) :
    selectedMatrix (characteristicSource Q) f =
      assignmentPolynomialMatrix Q f *
        Matrix.diagonal (assignmentColumnFactor f) := by
  classical
  ext i j
  simp only [Matrix.mul_apply, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single j]
  · cases hfj : f j with
    | inl s =>
        simp [selectedMatrix, characteristicSource, assignmentNumericMatrix,
          assignmentPolynomialMatrix, assignmentColumnFactor, hfj]
    | inr r =>
        simp [selectedMatrix, characteristicSource, assignmentNumericMatrix,
          assignmentPolynomialMatrix, assignmentColumnFactor, hfj]
  · intro k hk hkj
    simp [hkj]
  · simp

theorem det_selected_characteristic_matrix_factorization
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    (Q : SourceNetwork Species Reaction)
    (f : Species → Species ⊕ Reaction) :
    Matrix.det (selectedMatrix (characteristicSource Q) f) =
      C (Matrix.det (assignmentNumericMatrix Q f)) *
        ∏ j, assignmentColumnFactor f j := by
  classical
  rw [selected_characteristic_matrix_factorization Q f, Matrix.det_mul,
    Matrix.det_diagonal]
  change Matrix.det (assignmentPolynomialMatrix Q f) *
      ∏ j, assignmentColumnFactor f j = _
  rw [show Matrix.det (assignmentPolynomialMatrix Q f) =
      C (Matrix.det (assignmentNumericMatrix Q f)) by
    have hmap : assignmentPolynomialMatrix Q f =
        (assignmentNumericMatrix Q f).map Polynomial.C := by
      ext i j
      rfl
    rw [hmap]
    exact ((Polynomial.C : ℝ →+* ℝ[X]).map_det
      (assignmentNumericMatrix Q f)).symm]

/-- Inactive species, equivalently the identity columns of an augmented
assignment. -/
noncomputable def inactiveSpecies
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    (f : Species → Species ⊕ Reaction) : Finset Species := by
  classical
  exact Finset.univ.filter fun j => ¬(f j).isRight

theorem product_assignmentColumnFactor
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    (f : Species → Species ⊕ Reaction) :
    (∏ j, assignmentColumnFactor f j) =
      X ^ (inactiveSpecies f).card := by
  classical
  simp [assignmentColumnFactor, inactiveSpecies, Finset.prod_ite,
    Finset.prod_const]

/-- Real response scalar carried by an augmented assignment; identity choices
contribute one. -/
noncomputable def assignmentResponseScalar
    {Species Reaction : Type*} [Fintype Species]
    {Q : SourceNetwork Species Reaction} (R : Reactivity Q)
    (f : Species → Species ⊕ Reaction) : ℝ := by
  classical
  exact ∏ j, match f j with
    | Sum.inl _ => 1
    | Sum.inr r => R.value r j

theorem characteristicResponse_product_eq_C
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    [Fintype Reaction]
    (Q : SourceNetwork Species Reaction) (R : Reactivity Q)
    (f : Species → Species ⊕ Reaction)
    (hf : SupportedCharacteristicAssignment Q f) :
    (∏ j, characteristicResponse Q R (f j) j) =
      C (assignmentResponseScalar R f) := by
  classical
  rw [assignmentResponseScalar, map_prod]
  apply Finset.prod_congr rfl
  intro j hj
  cases hfj : f j with
  | inl s =>
      have hs := hf.2 j
      rw [hfj] at hs
      subst s
      simp [characteristicResponse]
  | inr r =>
      simp [characteristicResponse]

/-- A supported characteristic weight is exactly one monomial. -/
theorem supportedCharacteristicWeight_eq_monomial
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    [Fintype Reaction]
    (Q : SourceNetwork Species Reaction) (R : Reactivity Q)
    (f : Species → Species ⊕ Reaction)
    (hf : SupportedCharacteristicAssignment Q f) :
    supportedCharacteristicWeight Q R f =
      C (Matrix.det (assignmentNumericMatrix Q f) *
        assignmentResponseScalar R f) * X ^ (inactiveSpecies f).card := by
  classical
  rw [supportedCharacteristicWeight]
  simp only [hf, ↓reduceIte]
  rw [det_selected_characteristic_matrix_factorization Q f,
    product_assignmentColumnFactor f,
    characteristicResponse_product_eq_C Q R f hf, map_mul]
  ring

theorem negative_coefficient_of_C_mul_X_pow
    {a : ℝ} {m k : ℕ} (h : (C a * X ^ m).coeff k < 0) :
    k = m ∧ a < 0 := by
  by_cases hkm : k = m
  · subst k
    simpa using h
  · have hz : (C a * X ^ m).coeff k = 0 := by
      simp [hkm]
    rw [hz] at h
    linarith

theorem assignmentResponseScalar_pos
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    [Fintype Reaction]
    (Q : SourceNetwork Species Reaction) (R : Reactivity Q)
    (f : Species → Species ⊕ Reaction)
    (hf : SupportedCharacteristicAssignment Q f) :
    0 < assignmentResponseScalar R f := by
  classical
  rw [assignmentResponseScalar]
  apply Finset.prod_pos
  intro j hj
  cases hfj : f j with
  | inl s => simp
  | inr r =>
      apply R.positive_of_reactant
      have hs := hf.2 j
      simpa [hfj] using hs

theorem negative_supported_weight_coefficient_implies_det_negative
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    [Fintype Reaction]
    (Q : SourceNetwork Species Reaction) (R : Reactivity Q)
    (f : Species → Species ⊕ Reaction)
    (hf : SupportedCharacteristicAssignment Q f)
    {k : ℕ} (hneg : (supportedCharacteristicWeight Q R f).coeff k < 0) :
    Matrix.det (assignmentNumericMatrix Q f) < 0 := by
  rw [supportedCharacteristicWeight_eq_monomial Q R f hf] at hneg
  have hscalar := (negative_coefficient_of_C_mul_X_pow hneg).2
  have hresponse := assignmentResponseScalar_pos Q R f hf
  nlinarith

/-- Negative selected stoichiometry on the active species. -/
noncomputable def activeNegativeMatrix
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    (Q : SourceNetwork Species Reaction)
    (f : Species → Species ⊕ Reaction) :
    Matrix {j // j ∈ activeSpecies f} {j // j ∈ activeSpecies f} ℝ :=
  fun i j => -(Q.stoich i.1 (activeReaction f j) : ℝ)

theorem det_assignmentNumericMatrix_eq_det_activeNegativeMatrix
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    [Fintype Reaction]
    (Q : SourceNetwork Species Reaction)
    (f : Species → Species ⊕ Reaction)
    (hf : SupportedCharacteristicAssignment Q f) :
    Matrix.det (assignmentNumericMatrix Q f) =
      @Matrix.det {j : Species // j ∈ activeSpecies f} _
        (Subtype.fintype fun j => j ∈ activeSpecies f) ℝ _
        (activeNegativeMatrix Q f) := by
  classical
  have hzero : ∀ i, i ∈ activeSpecies f → ∀ j, j ∉ activeSpecies f →
      assignmentNumericMatrix Q f i j = 0 := by
    intro i hi j hj
    cases hfj : f j with
    | inl s =>
        have hs := hf.2 j
        rw [hfj] at hs
        subst s
        have hij : i ≠ j := by
          intro hij
          subst i
          exact hj hi
        simp [assignmentNumericMatrix, hfj, hij]
    | inr r =>
        exfalso
        apply hj
        simp [hfj]
  rw [Matrix.twoBlockTriangular_det'
    (assignmentNumericMatrix Q f) (fun j => j ∈ activeSpecies f) hzero]
  have hactive :
      (assignmentNumericMatrix Q f).toSquareBlockProp
          (fun j => j ∈ activeSpecies f) =
        activeNegativeMatrix Q f := by
    ext i j
    simp [Matrix.toSquareBlockProp, Matrix.toBlock,
      assignmentNumericMatrix, activeNegativeMatrix, assignment_eq_inr_activeReaction]
  have hinactive :
      (assignmentNumericMatrix Q f).toSquareBlockProp
          (fun j => j ∉ activeSpecies f) = 1 := by
    ext i j
    cases hfj : f j.1 with
    | inl s =>
        have hs := hf.2 j.1
        rw [hfj] at hs
        subst s
        by_cases hij : i = j
        · subst i
          simp only [Matrix.toSquareBlockProp, Matrix.toBlock,
            Matrix.submatrix_apply, Matrix.one_apply, assignmentNumericMatrix]
          rw [hfj]
          simp
        · have hval : i.1 ≠ j.1 := by
            intro hval
            exact hij (Subtype.ext hval)
          simp only [Matrix.toSquareBlockProp, Matrix.toBlock,
            Matrix.submatrix_apply, Matrix.one_apply, hij, assignmentNumericMatrix]
          rw [hfj]
          simp [hval]
    | inr r =>
        exfalso
        exact j.2 (by simp [hfj])
  rw [hactive, hinactive, Matrix.det_one, mul_one]

/-- Matrix determinant does not depend on which extensionally equal finite
enumeration instance is used for the index type. -/
theorem det_fintype_independent
    {ι : Type*} [DecidableEq ι] (F G : Fintype ι)
    (A : Matrix ι ι ℝ) :
    @Matrix.det ι _ F ℝ _ A = @Matrix.det ι _ G ℝ _ A := by
  have hFG : F = G := Subsingleton.elim F G
  subst G
  rfl

theorem negative_supported_weight_coefficient_implies_active_det_negative
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    [Fintype Reaction]
    (Q : SourceNetwork Species Reaction) (R : Reactivity Q)
    (f : Species → Species ⊕ Reaction)
    (hf : SupportedCharacteristicAssignment Q f)
    {k : ℕ} (hneg : (supportedCharacteristicWeight Q R f).coeff k < 0) :
    Matrix.det (activeNegativeMatrix Q f) < 0 := by
  have hfull := negative_supported_weight_coefficient_implies_det_negative
    Q R f hf hneg
  rw [det_assignmentNumericMatrix_eq_det_activeNegativeMatrix Q f hf] at hfull
  have henum := det_fintype_independent
    (Subtype.fintype fun j => j ∈ activeSpecies f)
    (Finset.Subtype.fintype (activeSpecies f))
    (activeNegativeMatrix Q f)
  linarith

@[simp] theorem supportedAssignmentChild_species
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    [Fintype Reaction] [DecidableEq Reaction]
    (Q : SourceNetwork Species Reaction)
    (f : Species → Species ⊕ Reaction)
    (hf : SupportedCharacteristicAssignment Q f) :
    (supportedAssignmentChild Q f hf).species = activeSpecies f := rfl

@[simp] theorem supportedAssignmentChild_assign_val
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    [Fintype Reaction] [DecidableEq Reaction]
    (Q : SourceNetwork Species Reaction)
    (f : Species → Species ⊕ Reaction)
    (hf : SupportedCharacteristicAssignment Q f)
    (j : (supportedAssignmentChild Q f hf).species) :
    ((supportedAssignmentChild Q f hf).assign j).1 = activeReaction f j := rfl

theorem activeNegativeMatrix_eq_neg_child_realMatrix
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    [Fintype Reaction] [DecidableEq Reaction]
    (Q : SourceNetwork Species Reaction)
    (f : Species → Species ⊕ Reaction)
    (hf : SupportedCharacteristicAssignment Q f) :
    activeNegativeMatrix Q f =
      -(supportedAssignmentChild Q f hf).realMatrix := by
  ext i j
  change -(Q.stoich i.1 (activeReaction f j) : ℝ) =
    -((Q.stoich i.1 ((supportedAssignmentChild Q f hf).assign j).1 : ℤ) : ℝ)
  erw [supportedAssignmentChild_assign_val]

end DUnstableCores

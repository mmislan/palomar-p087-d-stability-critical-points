module

public import proofs.DUnstableCores.CharacteristicLocalization
public import proofs.DUnstableCores.Minimality

@[expose] public section

/-!
# Positive-real localization

The first half of the localization theorem is purely ordered-polynomial:
a monic polynomial with a positive root has a negative coefficient.  The
source characteristic expansion then localizes that coefficient to one exact
supported partial child assignment.
-/

namespace DUnstableCores

open scoped BigOperators
open Polynomial

theorem monic_positive_root_has_negative_coefficient
    (p : ℝ[X]) (hmonic : p.Monic) {x : ℝ} (hx : 0 < x)
    (hroot : p.IsRoot x) :
    ∃ k : ℕ, p.coeff k < 0 := by
  by_contra hnone
  push Not at hnone
  have hterm_nonneg : ∀ k : ℕ, 0 ≤ p.coeff k * x ^ k := by
    intro k
    exact mul_nonneg (hnone k) (pow_nonneg (le_of_lt hx) k)
  have hlead : p.coeff p.natDegree = 1 := hmonic.coeff_natDegree
  have hleadterm : 0 < p.coeff p.natDegree * x ^ p.natDegree := by
    rw [hlead, one_mul]
    exact pow_pos hx _
  have hle : p.coeff p.natDegree * x ^ p.natDegree ≤
      ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * x ^ k := by
    exact Finset.single_le_sum (fun k _ => hterm_nonneg k) (by simp)
  have hsumpos : 0 < ∑ k ∈ Finset.range (p.natDegree + 1),
      p.coeff k * x ^ k := lt_of_lt_of_le hleadterm hle
  have heval : p.eval x = ∑ k ∈ Finset.range (p.natDegree + 1),
      p.coeff k * x ^ k := by
    simpa using p.eval_eq_sum_range x
  rw [← heval, hroot.eq_zero] at hsumpos
  exact (lt_irrefl 0) hsumpos

theorem HasPositiveRealEigenpair.isRoot_charpoly
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (h : HasPositiveRealEigenpair A) :
    ∃ lam : ℝ, 0 < lam ∧ A.charpoly.IsRoot lam := by
  classical
  rcases h with ⟨lam, v, hlam, hv, heq⟩
  let f : Module.End ℝ (ι → ℝ) := A.mulVecLin
  have hev : Module.End.HasEigenvector f lam v := by
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hv⟩
    funext i
    simpa [f, Matrix.mulVecLin_apply] using heq i
  have heval : Module.End.HasEigenvalue f lam :=
    Module.End.hasEigenvalue_of_hasEigenvector hev
  have hroot := (Module.End.hasEigenvalue_iff_isRoot_charpoly f lam).mp heval
  refine ⟨lam, hlam, ?_⟩
  simpa [f, Matrix.charpoly_mulVecLin] using hroot

theorem positiveRealEigenpair_has_negative_charpoly_coefficient
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (h : HasPositiveRealEigenpair A) :
    ∃ k : ℕ, A.charpoly.coeff k < 0 := by
  obtain ⟨lam, hlam, hroot⟩ := h.isRoot_charpoly
  exact monic_positive_root_has_negative_coefficient A.charpoly
    A.charpoly_monic hlam hroot

/-- Any negative source characteristic coefficient localizes to a single
negative supported augmented-assignment weight.  This is the ordered finite
sum core of positive-real localization, factored out for contraposition. -/
theorem negative_charpoly_coefficient_localizes_to_supported_weight
    {Species Reaction : Type*} [Fintype Species] [Fintype Reaction]
    [DecidableEq Species]
    (Q : SourceNetwork Species Reaction) (R : Reactivity Q) {k : ℕ}
    (hk : (Q.jacobian R).charpoly.coeff k < 0) :
    ∃ f : Species → Species ⊕ Reaction,
      SupportedCharacteristicAssignment Q f ∧
        (supportedCharacteristicWeight Q R f).coeff k < 0 := by
  have hcoeff := source_charpoly_coefficient_supported_assignment_sum Q R k
  rw [hcoeff] at hk
  have hexists : ∃ f : Species → Species ⊕ Reaction,
      (supportedCharacteristicWeight Q R f).coeff k < 0 := by
    by_contra hnone
    push Not at hnone
    have hsum : 0 ≤ ∑ f : Species → Species ⊕ Reaction,
        (supportedCharacteristicWeight Q R f).coeff k := by
      exact Finset.sum_nonneg fun f hf => hnone f
    linarith
  obtain ⟨f, hfneg⟩ := hexists
  refine ⟨f, ?_, hfneg⟩
  by_contra hsupport
  have hz : supportedCharacteristicWeight Q R f = 0 := by
    simp [supportedCharacteristicWeight, hsupport]
  rw [hz, coeff_zero] at hfneg
  linarith

theorem positiveRealEigenpair_localizes_to_negative_supported_weight
    {Species Reaction : Type*} [Fintype Species] [Fintype Reaction]
    [DecidableEq Species]
    (Q : SourceNetwork Species Reaction) (R : Reactivity Q)
    (h : HasPositiveRealEigenpair (Q.jacobian R)) :
    ∃ k : ℕ, ∃ f : Species → Species ⊕ Reaction,
      SupportedCharacteristicAssignment Q f ∧
        (supportedCharacteristicWeight Q R f).coeff k < 0 := by
  obtain ⟨k, hk⟩ := positiveRealEigenpair_has_negative_charpoly_coefficient h
  obtain ⟨f, hf, hfneg⟩ :=
    negative_charpoly_coefficient_localizes_to_supported_weight Q R hk
  exact ⟨k, f, hf, hfneg⟩

/-! ## Converting a supported augmented assignment to a literal child selection -/

/-- Species on which an augmented assignment chooses a reaction rather than
the characteristic identity column. -/
noncomputable def activeSpecies
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    (f : Species → Species ⊕ Reaction) : Finset Species := by
  classical
  exact Finset.univ.filter fun j => (f j).isRight

@[simp] theorem mem_activeSpecies_iff
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    (f : Species → Species ⊕ Reaction) (j : Species) :
    j ∈ activeSpecies f ↔ (f j).isRight := by
  classical
  simp [activeSpecies]

/-- The reaction selected at an active species. -/
noncomputable def activeReaction
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    (f : Species → Species ⊕ Reaction) (j : activeSpecies f) : Reaction :=
  (f j.1).getRight ((mem_activeSpecies_iff f j.1).mp j.2)

theorem assignment_eq_inr_activeReaction
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    (f : Species → Species ⊕ Reaction) (j : activeSpecies f) :
    f j.1 = Sum.inr (activeReaction f j) := by
  have hj := (mem_activeSpecies_iff f j.1).mp j.2
  cases hfj : f j.1 with
  | inl s => simp [hfj] at hj
  | inr r => simp [activeReaction, hfj]

/-- The reaction set used by the active part of an augmented assignment. -/
noncomputable def activeReactions
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    [Fintype Reaction] [DecidableEq Reaction]
    (f : Species → Species ⊕ Reaction) : Finset Reaction := by
  classical
  exact Finset.univ.image (activeReaction f)

/-- A supported augmented assignment canonically determines a literal source
child selection on its active species. -/
noncomputable def supportedAssignmentChild
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    [Fintype Reaction] [DecidableEq Reaction]
    (Q : SourceNetwork Species Reaction)
    (f : Species → Species ⊕ Reaction)
    (hf : SupportedCharacteristicAssignment Q f) : ChildSelection Q := by
  classical
  let g : {j // j ∈ activeSpecies f} → {r // r ∈ activeReactions f} :=
    fun j => ⟨activeReaction f j, by simp [activeReactions]⟩
  have ginj : Function.Injective g := by
    intro i j hij
    apply Subtype.ext
    apply hf.1
    rw [assignment_eq_inr_activeReaction f i,
      assignment_eq_inr_activeReaction f j]
    exact congrArg Sum.inr (congrArg Subtype.val hij)
  have gsurj : Function.Surjective g := by
    intro r
    have hr : r.1 ∈ activeReactions f := r.2
    simp only [activeReactions, Finset.mem_image, Finset.mem_univ, true_and] at hr
    obtain ⟨j, hj⟩ := hr
    refine ⟨j, ?_⟩
    apply Subtype.ext
    simpa [g] using hj
  exact {
    species := activeSpecies f
    reactions := activeReactions f
    assign := Equiv.ofBijective g ⟨ginj, gsurj⟩
    reactant_match := by
      intro j
      have hs := hf.2 j.1
      rw [assignment_eq_inr_activeReaction f j] at hs
      exact hs
  }

end DUnstableCores

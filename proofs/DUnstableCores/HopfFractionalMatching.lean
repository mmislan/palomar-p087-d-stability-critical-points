module

public import proofs.DUnstableCores.HopfBoundary

@[expose] public section

/-!
# Fractional child-assignment obstruction at the Hopf wall

An injective child assignment uses any reaction at most once.  Consequently,
every convex mixture of such assignments has reaction-row load at most one.
The normalized reactivity of the exact Hopf source violates this capacity at
its shared consumption reaction, locating the information lost by a naive
matching decomposition.
-/

namespace DUnstableCores

open scoped BigOperators

def assignmentIncidence {Species Reaction : Type*} [DecidableEq Reaction]
    (f : Species → Reaction) (r : Reaction) (s : Species) : ℝ :=
  if f s = r then 1 else 0

structure FractionalInjectiveMixture
    {Species Reaction : Type*} [Fintype Species] [Fintype Reaction]
    [DecidableEq Species] [DecidableEq Reaction]
    (M : Matrix Reaction Species ℝ) where
  weight : (Species → Reaction) → ℝ
  weight_nonneg : ∀ f, 0 ≤ weight f
  weight_total : ∑ f, weight f = 1
  injective_of_pos : ∀ f, 0 < weight f → Function.Injective f
  expansion : ∀ r s,
    M r s = ∑ f, weight f * assignmentIncidence f r s

theorem injective_assignment_row_capacity
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Reaction]
    (f : Species → Reaction) (hf : Function.Injective f) (r : Reaction) :
    ∑ s, assignmentIncidence f r s ≤ 1 := by
  let support := Finset.univ.filter (fun s => f s = r)
  have hcard : support.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have ha' : f a = r := (Finset.mem_filter.mp ha).2
    have hb' : f b = r := (Finset.mem_filter.mp hb).2
    exact hf (ha'.trans hb'.symm)
  have hsum :
      (∑ s, assignmentIncidence f r s) = (support.card : ℝ) := by
    simp [assignmentIncidence, support]
  rw [hsum]
  exact_mod_cast hcard

theorem FractionalInjectiveMixture.row_capacity
    {Species Reaction : Type*} [Fintype Species] [Fintype Reaction]
    [DecidableEq Species] [DecidableEq Reaction]
    {M : Matrix Reaction Species ℝ}
    (C : FractionalInjectiveMixture M) (r : Reaction) :
    ∑ s, M r s ≤ 1 := by
  calc
    ∑ s, M r s =
        ∑ s, ∑ f, C.weight f * assignmentIncidence f r s := by
          apply Finset.sum_congr rfl
          intro s _
          exact C.expansion r s
    _ = ∑ f, C.weight f * ∑ s, assignmentIncidence f r s := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro f _
          rw [Finset.mul_sum]
    _ ≤ ∑ f, C.weight f * 1 := by
          apply Finset.sum_le_sum
          intro f _
          by_cases hz : C.weight f = 0
          · simp [hz]
          · have hpos : 0 < C.weight f :=
              lt_of_le_of_ne (C.weight_nonneg f) (Ne.symm hz)
            exact mul_le_mul_of_nonneg_left
              (injective_assignment_row_capacity f
                (C.injective_of_pos f hpos) r)
              (C.weight_nonneg f)
    _ = 1 := by simpa using C.weight_total

noncomputable def hopfNormalizedReactivity4 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1 / 2, 0, 0, 0;
     0, 1 / 2, 0, 0;
     0, 0, 1 / 2, 0;
     1 / 2, 1 / 2, 1 / 2, 1]

theorem hopfNormalizedReactivity4_shared_load :
    ∑ s, hopfNormalizedReactivity4 3 s = (5 : ℝ) / 2 := by
  rw [Fin.sum_univ_four]
  simp [hopfNormalizedReactivity4]
  norm_num

theorem hopfNormalizedReactivity4_not_fractional_injective :
    ¬ Nonempty (FractionalInjectiveMixture hopfNormalizedReactivity4) := by
  rintro ⟨C⟩
  have hcap := C.row_capacity 3
  rw [hopfNormalizedReactivity4_shared_load] at hcap
  norm_num at hcap

end DUnstableCores

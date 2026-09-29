module

public import proofs.DUnstableCores.HopfSchur

@[expose] public section

/-!
# Source-faithful lifting of the local Hopf alternative

This file deliberately retains the literal reaction vertex.  In particular,
a positive Jacobian diagonal is localized to an actual reactant reaction with
positive net stoichiometry before a singleton child is constructed.
-/

namespace DUnstableCores

open scoped BigOperators

noncomputable def singletonEquiv
    {Species Reaction : Type*} [DecidableEq Species] [DecidableEq Reaction]
    (i : Species) (r : Reaction) :
    {x // x ∈ ({i} : Finset Species)} ≃
      {q // q ∈ ({r} : Finset Reaction)} :=
  Equiv.ofUnique _ _

noncomputable def singletonChild
    {Species Reaction : Type*} [DecidableEq Species] [DecidableEq Reaction]
    (Q : SourceNetwork Species Reaction) (i : Species) (r : Reaction)
    (hr : Q.Reactant i r) : ChildSelection Q where
  species := {i}
  reactions := {r}
  assign := singletonEquiv i r
  reactant_match := by
    intro x
    have hx : x.1 = i := Finset.mem_singleton.mp x.2
    have har : (singletonEquiv i r x).1 = r :=
      Finset.mem_singleton.mp (singletonEquiv i r x).2
    change Q.Reactant x.1 (singletonEquiv i r x).1
    rw [hx, har]
    exact hr

theorem singletonChild_realMatrix_entry
    {Species Reaction : Type*} [DecidableEq Species] [DecidableEq Reaction]
    (Q : SourceNetwork Species Reaction) (i : Species) (r : Reaction)
    (hr : Q.Reactant i r) (x y : (singletonChild Q i r hr).species) :
    (singletonChild Q i r hr).realMatrix x y = (Q.stoich i r : ℝ) := by
  have hx : x.1 = i := Finset.mem_singleton.mp x.2
  have har : ((singletonChild Q i r hr).assign y).1 = r :=
    Finset.mem_singleton.mp ((singletonChild Q i r hr).assign y).2
  simp only [ChildSelection.realMatrix, ChildSelection.matrix_eq_stoich]
  rw [hx, har]

theorem positive_reactant_stoich_yields_singleton_core
    {Species Reaction : Type*} [DecidableEq Species] [DecidableEq Reaction]
    (Q : SourceNetwork Species Reaction) (i : Species) (r : Reaction)
    (hr : Q.Reactant i r) (hstoich : 0 < (Q.stoich i r : ℝ)) :
    ∃ core : ChildSelection Q, IsDUnstableCore core := by
  let child := singletonChild Q i r hr
  let k : child.species := ⟨i, by simp [child, singletonChild]⟩
  let : Unique child.species := {
    default := k
    uniq := by
      intro x
      apply Subtype.ext
      have hx : x.1 ∈ ({i} : Finset Species) := by
        exact x.2
      exact Finset.mem_singleton.mp hx
  }
  have hdet : Matrix.det (-child.realMatrix) < 0 := by
    rw [Matrix.det_eq_elem_of_subsingleton (-child.realMatrix) k]
    change -(singletonChild Q i r hr).realMatrix k k < 0
    have hentry := singletonChild_realMatrix_entry Q i r hr k k
    rw [hentry]
    linarith
  have hchild : DUnstable child.realMatrix :=
    det_neg_negative_implies_dUnstable child.realMatrix hdet
  obtain ⟨core, _, hcore⟩ := dUnstable_childSelection_contains_core child hchild
  exact ⟨core, hcore⟩

theorem positive_jacobian_diagonal_localizes_to_reaction
    {Species Reaction : Type*} [Fintype Reaction]
    (Q : SourceNetwork Species Reaction) (R : Reactivity Q) (i : Species)
    (hdiag : 0 < Q.jacobian R i i) :
    ∃ r : Reaction, Q.Reactant i r ∧ 0 < (Q.stoich i r : ℝ) := by
  by_contra hnone
  push Not at hnone
  have hterm : ∀ r : Reaction,
      (Q.stoich i r : ℝ) * R.value r i ≤ 0 := by
    intro r
    by_cases hr : Q.Reactant i r
    · exact mul_nonpos_of_nonpos_of_nonneg
        (hnone r hr) (R.nonneg r i)
    · rw [R.zero_of_not_reactant r i hr]
      simp
  have hsum : (∑ r : Reaction,
      (Q.stoich i r : ℝ) * R.value r i) ≤ 0 := by
    exact Finset.sum_nonpos fun r _ => hterm r
  rw [Q.jacobian_apply R i i] at hdiag
  linarith

/-- A positive Jacobian diagonal produces a literal source child core. -/
theorem positive_jacobian_diagonal_yields_singleton_core
    {Species Reaction : Type*} [Fintype Reaction]
    [DecidableEq Species] [DecidableEq Reaction]
    (Q : SourceNetwork Species Reaction) (R : Reactivity Q) (i : Species)
    (hdiag : 0 < Q.jacobian R i i) :
    ∃ core : ChildSelection Q, IsDUnstableCore core := by
  obtain ⟨r, hr, hs⟩ :=
    positive_jacobian_diagonal_localizes_to_reaction Q R i hdiag
  exact positive_reactant_stoich_yields_singleton_core Q i r hr hs

/--
A literal source-level opposite-sign two-species interaction circuit.  The
reaction vertices remain explicit; the two disjuncts record its orientation.
-/
def HasLiteralOppositeSignCircuit
    {Species Reaction : Type*} (Q : SourceNetwork Species Reaction)
    (i j : Species) : Prop :=
  (∃ rp rn : Reaction,
      Q.Reactant j rp ∧ 0 < (Q.stoich i rp : ℝ) ∧
      Q.Reactant i rn ∧ (Q.stoich j rn : ℝ) < 0) ∨
  (∃ rn rp : Reaction,
      Q.Reactant j rn ∧ (Q.stoich i rn : ℝ) < 0 ∧
      Q.Reactant i rp ∧ 0 < (Q.stoich j rp : ℝ))

theorem positive_jacobian_entry_localizes_to_reaction
    {Species Reaction : Type*} [Fintype Reaction]
    (Q : SourceNetwork Species Reaction) (R : Reactivity Q) (i j : Species)
    (hentry : 0 < Q.jacobian R i j) :
    ∃ r : Reaction, Q.Reactant j r ∧ 0 < (Q.stoich i r : ℝ) := by
  by_contra hnone
  push Not at hnone
  have hterm : ∀ r : Reaction,
      (Q.stoich i r : ℝ) * R.value r j ≤ 0 := by
    intro r
    by_cases hr : Q.Reactant j r
    · exact mul_nonpos_of_nonpos_of_nonneg (hnone r hr) (R.nonneg r j)
    · rw [R.zero_of_not_reactant r j hr]
      simp
  have hsum : (∑ r : Reaction,
      (Q.stoich i r : ℝ) * R.value r j) ≤ 0 :=
    Finset.sum_nonpos fun r _ => hterm r
  rw [Q.jacobian_apply R i j] at hentry
  linarith

theorem negative_jacobian_entry_localizes_to_reaction
    {Species Reaction : Type*} [Fintype Reaction]
    (Q : SourceNetwork Species Reaction) (R : Reactivity Q) (i j : Species)
    (hentry : Q.jacobian R i j < 0) :
    ∃ r : Reaction, Q.Reactant j r ∧ (Q.stoich i r : ℝ) < 0 := by
  by_contra hnone
  push Not at hnone
  have hterm : ∀ r : Reaction,
      0 ≤ (Q.stoich i r : ℝ) * R.value r j := by
    intro r
    by_cases hr : Q.Reactant j r
    · exact mul_nonneg (hnone r hr) (R.nonneg r j)
    · rw [R.zero_of_not_reactant r j hr]
      simp
  have hsum : 0 ≤ (∑ r : Reaction,
      (Q.stoich i r : ℝ) * R.value r j) :=
    Finset.sum_nonneg fun r _ => hterm r
  rw [Q.jacobian_apply R i j] at hentry
  linarith

theorem negative_jacobian_two_cycle_yields_literal_circuit
    {Species Reaction : Type*} [Fintype Reaction]
    (Q : SourceNetwork Species Reaction) (R : Reactivity Q) (i j : Species)
    (hcycle : Q.jacobian R i j * Q.jacobian R j i < 0) :
    HasLiteralOppositeSignCircuit Q i j := by
  rcases (mul_neg_iff.mp hcycle) with h | h
  · obtain ⟨rp, hjp, hip⟩ :=
      positive_jacobian_entry_localizes_to_reaction Q R i j h.1
    obtain ⟨rn, hin, hjn⟩ :=
      negative_jacobian_entry_localizes_to_reaction Q R j i h.2
    exact Or.inl ⟨rp, rn, hjp, hip, hin, hjn⟩
  · obtain ⟨rn, hjn, hin⟩ :=
      negative_jacobian_entry_localizes_to_reaction Q R i j h.1
    obtain ⟨rp, hip, hjp⟩ :=
      positive_jacobian_entry_localizes_to_reaction Q R j i h.2
    exact Or.inr ⟨rn, rp, hjn, hin, hip, hjp⟩

/--
The source-faithful two-species base case of the Hopf-support alternative:
an exact singleton Schur branch yields either a literal D-unstable source core
or an uncompressed opposite-sign interaction circuit.
-/
theorem singleton_hopf_source_local_or_literal_circuit
    {Species Reaction : Type*} [Fintype Reaction]
    [DecidableEq Species] [DecidableEq Reaction]
    (Q : SourceNetwork Species Reaction) (R : Reactivity Q) (i j : Species)
    (ω : ℝ)
    (w : HopfBranchSolveWitness (Q.jacobian R i i)
      (fun _ : Unit => Q.jacobian R i j)
      (fun _ : Unit => Q.jacobian R j i)
      (fun _ _ : Unit => Q.jacobian R j j) ω)
    (hω : 0 < ω) :
    (∃ core : ChildSelection Q, IsDUnstableCore core) ∨
      HasLiteralOppositeSignCircuit Q i j := by
  rcases w.singleton_positive_diagonal_or_phase_cycle hω with hi | hj | hc
  · exact Or.inl (positive_jacobian_diagonal_yields_singleton_core Q R i hi)
  · exact Or.inl (positive_jacobian_diagonal_yields_singleton_core Q R j hj)
  · right
    exact negative_jacobian_two_cycle_yields_literal_circuit Q R i j hc.2.2

end DUnstableCores

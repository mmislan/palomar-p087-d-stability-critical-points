module

public import proofs.DUnstableCores.CICAdapter
public import proofs.AutocatalyticCS.SourceSemantics
public import Mathlib.Combinatorics.Hall.Finite

@[expose] public section

/-!
# Exact matching dichotomy on a minimal Hurwitz cycle

This file keeps the two notions which must not be conflated separate:
`CICAdapter` records factor ownership, while the relation below records the
literal reactions eligible for a child selection.  Hall's theorem either
selects distinct eligible reactions or returns a cardinality obstruction.
-/

namespace DUnstableCores

/-- Species moved by the selected single cycle. -/
abbrev CycleSupport {Species : Type*} [Fintype Species] [DecidableEq Species]
    (tau : Equiv.Perm Species) := {i : Species // i ∈ tau.support}

/-- A reaction can witness a cycle edge only when its tail species is a
literal reactant and its stoichiometric column is nonzero at the head. -/
def LiteralCycleWitness
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    (Q : SourceNetwork Species Reaction) (tau : Equiv.Perm Species)
    (i : CycleSupport tau) (q : Reaction) : Prop :=
  Q.Reactant i.1 q ∧ (Q.stoich (tau i.1) q : ℝ) ≠ 0

/-- The finite reaction neighborhood of a set of moved cycle species. -/
noncomputable def cycleWitnessNeighborhood
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    [Fintype Reaction]
    (Q : SourceNetwork Species Reaction) (tau : Equiv.Perm Species)
    (A : Finset (CycleSupport tau)) : Finset Reaction := by
  classical
  exact Finset.univ.filter fun q : Reaction =>
    ∃ i ∈ A, LiteralCycleWitness Q tau i q

theorem minimal_hurwitz_cycle_witness_nonempty
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    [Fintype Reaction]
    {Q : SourceNetwork Species Reaction} {R : Reactivity Q} {lam : ℂ}
    (C : MinimalHurwitzInteractionCircuit Q R lam) :
    ∀ i : CycleSupport C.cycle, ∃ q : Reaction,
      LiteralCycleWitness Q C.cycle i q := by
  intro i
  have hi : C.cycle i.1 ≠ i.1 := Equiv.Perm.mem_support.mp i.2
  exact C.literal_edges i.1 hi

/-- Hall's condition is exactly equivalent to distinct literal reaction
witnesses on the cycle support. -/
theorem minimal_hurwitz_cycle_hall_iff_injective_witnesses
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    [Fintype Reaction] [DecidableEq Reaction]
    {Q : SourceNetwork Species Reaction} {R : Reactivity Q} {lam : ℂ}
    (C : MinimalHurwitzInteractionCircuit Q R lam) :
    (∀ A : Finset (CycleSupport C.cycle), A.card ≤
        (cycleWitnessNeighborhood Q C.cycle A).card) ↔
      ∃ witness : CycleSupport C.cycle → Reaction,
        Function.Injective witness ∧
        ∀ i, LiteralCycleWitness Q C.cycle i (witness i) := by
  classical
  simpa [cycleWitnessNeighborhood] using
    (Fintype.all_card_le_filter_rel_iff_exists_injective
      (LiteralCycleWitness Q C.cycle))

/-- The injective Hall branch is not merely a factor assignment: it constructs
an actual source-valid child selection on precisely the moved cycle species. -/
theorem childSelection_of_injective_cycle_witnesses
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    [Fintype Reaction] [DecidableEq Reaction]
    (Q : SourceNetwork Species Reaction) (tau : Equiv.Perm Species)
    (witness : CycleSupport tau → Reaction)
    (hinj : Function.Injective witness)
    (heligible : ∀ i, LiteralCycleWitness Q tau i (witness i)) :
    ∃ child : ChildSelection Q, child.species = tau.support := by
  classical
  let e := Fintype.equivFin (CycleSupport tau)
  let matching : AutocatalyticCS.IndexedMatching Q.toReactionNetwork :=
    { card := Fintype.card (CycleSupport tau)
      left := fun k => (e.symm k).1
      right := fun k => witness (e.symm k)
      left_injective := by
        intro a b hab
        apply e.symm.injective
        exact Subtype.ext hab
      right_injective := by
        intro a b hab
        exact e.symm.injective (hinj hab)
      reactant_edge := by
        intro k
        exact (heligible (e.symm k)).1 }
  refine ⟨matching.toChildSelection, ?_⟩
  change matching.species = tau.support
  change (Finset.univ.image fun k => (e.symm k).1) = tau.support
  ext i
  constructor
  · intro hi
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hi
    exact (e.symm k).2
  · intro hi
    apply Finset.mem_image.mpr
    refine ⟨e ⟨i, hi⟩, Finset.mem_univ _, ?_⟩
    simp

/-- Exact finite dichotomy: either the cycle admits a source matching, or a
specific subset has too few eligible literal reactions. -/
theorem minimal_hurwitz_cycle_matching_or_hall_defect
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    [Fintype Reaction] [DecidableEq Reaction]
    {Q : SourceNetwork Species Reaction} {R : Reactivity Q} {lam : ℂ}
    (C : MinimalHurwitzInteractionCircuit Q R lam) :
    (∃ witness : CycleSupport C.cycle → Reaction,
        Function.Injective witness ∧
        ∀ i, LiteralCycleWitness Q C.cycle i (witness i)) ∨
      ∃ A : Finset (CycleSupport C.cycle),
        (cycleWitnessNeighborhood Q C.cycle A).card < A.card := by
  classical
  by_cases hHall : ∀ A : Finset (CycleSupport C.cycle), A.card ≤
      (cycleWitnessNeighborhood Q C.cycle A).card
  · exact Or.inl ((minimal_hurwitz_cycle_hall_iff_injective_witnesses C).mp hHall)
  · right
    push Not at hHall
    exact hHall

/-- Hall's condition therefore yields a genuine child selection supported on
the selected phase-carrying cycle. -/
theorem minimal_hurwitz_cycle_hall_yields_childSelection
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    [Fintype Reaction] [DecidableEq Reaction]
    {Q : SourceNetwork Species Reaction} {R : Reactivity Q} {lam : ℂ}
    (C : MinimalHurwitzInteractionCircuit Q R lam)
    (hHall : ∀ A : Finset (CycleSupport C.cycle), A.card ≤
      (cycleWitnessNeighborhood Q C.cycle A).card) :
    ∃ child : ChildSelection Q, child.species = C.cycle.support := by
  obtain ⟨witness, hinj, heligible⟩ :=
    (minimal_hurwitz_cycle_hall_iff_injective_witnesses C).mp hHall
  exact childSelection_of_injective_cycle_witnesses
    Q C.cycle witness hinj heligible

end DUnstableCores

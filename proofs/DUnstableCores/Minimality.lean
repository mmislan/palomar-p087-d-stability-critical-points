module

public import proofs.DUnstableCores.Source
public import proofs.DUnstableCores.DScaling

@[expose] public section

/-!
# Principal-minimal D-unstable child selections

Minimality is a finite-cardinality theorem.  It does not depend on how the
existential D-instability witness was discovered.
-/

namespace DUnstableCores

variable {Species Reaction : Type*}
variable [DecidableEq Species] [DecidableEq Reaction]
variable {Q : SourceNetwork Species Reaction}

namespace ChildSelection

/-- The real child matrix used by the spectral predicates. -/
def realMatrix (κ : ChildSelection Q) : Matrix κ.species κ.species ℝ :=
  fun i j => (κ.matrix i j : ℝ)

theorem restricts_refl (κ : ChildSelection Q) : κ.Restricts κ := by
  refine ⟨Finset.Subset.rfl, Finset.Subset.rfl, ?_⟩
  intro x y hxy
  have hsub : x = y := Subtype.ext hxy
  simp [hsub]

theorem restricts_trans {small middle large : ChildSelection Q}
    (hsm : small.Restricts middle) (hml : middle.Restricts large) :
    small.Restricts large := by
  refine ⟨hsm.1.trans hml.1, hsm.2.1.trans hml.2.1, ?_⟩
  intro x z hxz
  let y : {s // s ∈ middle.species} := ⟨x.1, hsm.1 x.2⟩
  calc
    (small.assign x).1 = (middle.assign y).1 := hsm.2.2 x y rfl
    _ = (large.assign z).1 := hml.2.2 y z hxz

end ChildSelection

/-- Principal-minimality inside the source child-selection restriction order. -/
def IsDUnstableCore (κ : ChildSelection Q) : Prop :=
  DUnstable κ.realMatrix ∧
    ∀ small : ChildSelection Q,
      small.Restricts κ → small.species ⊂ κ.species →
        ¬ DUnstable small.realMatrix

/-- Every D-unstable child selection contains a principal-minimal D-unstable
restriction.  The proof minimizes species cardinality among all D-unstable
restrictions of the given child selection. -/
theorem dUnstable_childSelection_contains_core (κ : ChildSelection Q)
    (hκ : DUnstable κ.realMatrix) :
    ∃ core : ChildSelection Q, core.Restricts κ ∧ IsDUnstableCore core := by
  classical
  let BadSize : Nat → Prop := fun n =>
    ∃ candidate : ChildSelection Q,
      candidate.Restricts κ ∧ DUnstable candidate.realMatrix ∧
        candidate.species.card = n
  have hBadSize : ∃ n, BadSize n := by
    exact ⟨κ.species.card, κ, ChildSelection.restricts_refl κ, hκ, rfl⟩
  let size := Nat.find hBadSize
  obtain ⟨core, hcoreκ, hcoreD, hcoreCard⟩ := Nat.find_spec hBadSize
  refine ⟨core, hcoreκ, hcoreD, ?_⟩
  intro small hsmallCore hproper hsmallD
  have hsmallκ : small.Restricts κ :=
    ChildSelection.restricts_trans hsmallCore hcoreκ
  have hsmallBad : BadSize small.species.card :=
    ⟨small, hsmallκ, hsmallD, rfl⟩
  have hsizeLe : size ≤ small.species.card :=
    Nat.find_min' hBadSize hsmallBad
  have hsmallLt : small.species.card < size := by
    have := Finset.card_lt_card hproper
    simpa [size, hcoreCard] using this
  omega

end DUnstableCores

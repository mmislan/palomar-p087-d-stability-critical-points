module

public import Mathlib
public import proofs.AutocatalyticCS.Basic

@[expose] public section

/-!
# Source-faithful semantics for the D-unstable-cores campaign

This file freezes the literature-facing source contract before any spectral
argument is attempted.  Reactant incidence is data, not something inferred
from the net stoichiometric matrix.  Explicit catalysts are retained even
though their net stoichiometric contribution can vanish.
-/

namespace DUnstableCores

open scoped BigOperators

/-- A finite literal reaction source.  `catalyst` is an explicit source label;
the two inequalities say that every labelled catalyst occurs on both sides of
the reaction. -/
structure SourceNetwork (Species Reaction : Type*) where
  reactant : Matrix Species Reaction ℕ
  product : Matrix Species Reaction ℕ
  catalyst : Matrix Species Reaction ℕ
  catalyst_le_reactant : ∀ s r, catalyst s r ≤ reactant s r
  catalyst_le_product : ∀ s r, catalyst s r ≤ product s r

namespace SourceNetwork

variable {Species Reaction : Type*}

/-- The literal integer stoichiometric matrix. -/
def stoich (Q : SourceNetwork Species Reaction) : Matrix Species Reaction ℤ :=
  fun s r => (Q.product s r : ℤ) - (Q.reactant s r : ℤ)

/-- Forget only the explicit catalyst label, never its reactant multiplicity. -/
def toReactionNetwork (Q : SourceNetwork Species Reaction) :
    AutocatalyticCS.ReactionNetwork Species Reaction where
  reactant := Q.reactant
  product := Q.product

@[simp] theorem toReactionNetwork_net (Q : SourceNetwork Species Reaction)
    (s : Species) (r : Reaction) :
    Q.toReactionNetwork.net s r = Q.stoich s r := rfl

/-- Source-allowed derivative coordinates are exactly reactant incidences. -/
def Reactant (Q : SourceNetwork Species Reaction) (s : Species) (r : Reaction) : Prop :=
  0 < Q.reactant s r

/-- Explicit catalyst incidence remains queryable even if `stoich s r = 0`. -/
def IsCatalyst (Q : SourceNetwork Species Reaction) (s : Species) (r : Reaction) : Prop :=
  0 < Q.catalyst s r

theorem reactant_of_catalyst (Q : SourceNetwork Species Reaction)
    {s : Species} {r : Reaction} (h : Q.IsCatalyst s r) : Q.Reactant s r := by
  exact lt_of_lt_of_le h (Q.catalyst_le_reactant s r)

end SourceNetwork

variable {Species Reaction : Type*}

/-- Reuse the already verified finite matching semantics on the literal source. -/
abbrev ChildSelection (Q : SourceNetwork Species Reaction) :=
  AutocatalyticCS.ChildSelection Q.toReactionNetwork

namespace ChildSelection

variable {Q : SourceNetwork Species Reaction}

/-- Principal restriction uses species inclusion and the same assignment on
the retained species, exactly as in the imported source matching layer. -/
abbrev Restricts [DecidableEq Species] [DecidableEq Reaction]
    (small large : ChildSelection Q) : Prop :=
  AutocatalyticCS.ChildSelection.Restricts small large

@[simp] theorem matrix_eq_stoich [DecidableEq Species] [DecidableEq Reaction]
    (κ : ChildSelection Q) (i j : κ.species) :
    κ.matrix i j = Q.stoich i.1 (κ.assign j).1 := rfl

end ChildSelection

/-- An independently tunable parameter-rich reactivity matrix.  Positivity is
allowed exactly on reactant coordinates; forbidden coordinates are zero. -/
structure Reactivity (Q : SourceNetwork Species Reaction) where
  value : Matrix Reaction Species ℝ
  nonneg : ∀ r s, 0 ≤ value r s
  positive_of_reactant : ∀ r s, Q.Reactant s r → 0 < value r s
  zero_of_not_reactant : ∀ r s, ¬ Q.Reactant s r → value r s = 0

namespace Reactivity

variable {Q : SourceNetwork Species Reaction}

theorem positive_iff (R : Reactivity Q) (r : Reaction) (s : Species) :
    0 < R.value r s ↔ Q.Reactant s r := by
  constructor
  · intro h
    by_contra hreact
    rw [R.zero_of_not_reactant r s hreact] at h
    exact (lt_irrefl 0) h
  · exact R.positive_of_reactant r s

theorem zero_iff (R : Reactivity Q) (r : Reaction) (s : Species) :
    R.value r s = 0 ↔ ¬ Q.Reactant s r := by
  constructor
  · intro hz hreact
    have hp := R.positive_of_reactant r s hreact
    rw [hz] at hp
    exact (lt_irrefl 0) hp
  · exact R.zero_of_not_reactant r s

end Reactivity

namespace SourceNetwork

variable [Fintype Reaction]

/-- Literature consistency: the stoichiometric matrix admits a strictly
positive reaction-flux vector in its kernel.  This is the standing source
hypothesis needed for a positive equilibrium in the original conjecture. -/
def Consistent (Q : SourceNetwork Species Reaction) : Prop :=
  ∃ flux : Reaction → ℝ,
    (∀ r, 0 < flux r) ∧
      ∀ s, ∑ r : Reaction, (Q.stoich s r : ℝ) * flux r = 0

/-- The parameter-rich Jacobian is literally `S R`. -/
def jacobian (Q : SourceNetwork Species Reaction) (R : Reactivity Q) :
    Matrix Species Species ℝ :=
  fun i j => ∑ r : Reaction, (Q.stoich i r : ℝ) * R.value r j

theorem jacobian_apply (Q : SourceNetwork Species Reaction) (R : Reactivity Q)
    (i j : Species) :
    Q.jacobian R i j = ∑ r : Reaction, (Q.stoich i r : ℝ) * R.value r j := by
  rfl

end SourceNetwork

/-- The two public contracts are deliberately distinct tags. -/
inductive ContractScope
  | parameterRich
  | classicalMassAction
  deriving DecidableEq, Repr

@[simp] theorem parameterRich_ne_classicalMassAction :
    ContractScope.parameterRich ≠ ContractScope.classicalMassAction := by
  decide

/-- One admissible parameter-rich instance. -/
structure ParameterRichInstance (Q : SourceNetwork Species Reaction) where
  reactivity : Reactivity Q

/-- Classical fixed-exponent mass action carries coupled concentration and
rate data in addition to its induced admissible derivative matrix.  The
coupling equation is retained as data; it is not silently assumed for an
arbitrary parameter-rich reactivity. -/
structure ClassicalMassActionInstance [Fintype Species]
    (Q : SourceNetwork Species Reaction) where
  concentration : Species → ℝ
  rateConstant : Reaction → ℝ
  concentration_pos : ∀ s, 0 < concentration s
  rateConstant_pos : ∀ r, 0 < rateConstant r
  reactivity : Reactivity Q
  derivative_formula : ∀ r s,
    reactivity.value r s =
      (Q.reactant s r : ℝ) *
        (rateConstant r * ∏ t : Species, concentration t ^ Q.reactant t r) /
          concentration s

def ClassicalMassActionInstance.toParameterRich [Fintype Species]
    {Q : SourceNetwork Species Reaction} (M : ClassicalMassActionInstance Q) :
    ParameterRichInstance Q :=
  ⟨M.reactivity⟩

namespace Regression

abbrev OneSpecies := Fin 1
abbrev OneReaction := Fin 1

/-- A species occurring catalytically in the unique reaction. -/
def catalyticIdentity : SourceNetwork OneSpecies OneReaction where
  reactant := fun _ _ => 1
  product := fun _ _ => 1
  catalyst := fun _ _ => 1
  catalyst_le_reactant := by simp
  catalyst_le_product := by simp

/-- The net-identical source in which the species does not occur at all. -/
def silentIdentity : SourceNetwork OneSpecies OneReaction where
  reactant := fun _ _ => 0
  product := fun _ _ => 0
  catalyst := fun _ _ => 0
  catalyst_le_reactant := by simp
  catalyst_le_product := by simp

theorem catalytic_and_silent_have_equal_stoich :
    catalyticIdentity.stoich = silentIdentity.stoich := by
  ext s r
  simp [SourceNetwork.stoich, catalyticIdentity, silentIdentity]

theorem catalytic_reactant_visible : catalyticIdentity.Reactant 0 0 := by
  simp [SourceNetwork.Reactant, catalyticIdentity]

theorem silent_reactant_absent : ¬ silentIdentity.Reactant 0 0 := by
  simp [SourceNetwork.Reactant, silentIdentity]

/-- Equal net stoichiometry does not determine allowed reactivity support. -/
theorem catalyst_erasure_regression :
    catalyticIdentity.stoich = silentIdentity.stoich ∧
      catalyticIdentity.Reactant 0 0 ∧ ¬ silentIdentity.Reactant 0 0 := by
  exact ⟨catalytic_and_silent_have_equal_stoich,
    catalytic_reactant_visible, silent_reactant_absent⟩

/-- A widened derivative domain is rejected: the silent source forces its
unique forbidden reactivity coordinate to vanish. -/
theorem forbidden_reactivity_regression (R : Reactivity silentIdentity) :
    R.value 0 0 = 0 := by
  exact R.zero_of_not_reactant 0 0 silent_reactant_absent

abbrev TwoReactions := Fin 2

/-- Both reactions have identical reactant support but opposite net columns. -/
def matchingOrderSource : SourceNetwork OneSpecies TwoReactions where
  reactant := fun _ _ => 1
  product := fun _ r => if r = 0 then 2 else 0
  catalyst := fun _ _ => 0
  catalyst_le_reactant := by simp
  catalyst_le_product := by simp

def chooseReactionZero :
    {s // s ∈ ({0} : Finset OneSpecies)} ≃
      {r // r ∈ ({0} : Finset TwoReactions)} where
  toFun := fun _ => ⟨0, by simp⟩
  invFun := fun _ => ⟨0, by simp⟩
  left_inv := by intro x; ext; simp
  right_inv := by
    intro r
    apply Subtype.ext
    exact (Finset.mem_singleton.mp r.property).symm

def chooseReactionOne :
    {s // s ∈ ({0} : Finset OneSpecies)} ≃
      {r // r ∈ ({1} : Finset TwoReactions)} where
  toFun := fun _ => ⟨1, by simp⟩
  invFun := fun _ => ⟨0, by simp⟩
  left_inv := by intro x; ext; simp
  right_inv := by
    intro r
    apply Subtype.ext
    exact (Finset.mem_singleton.mp r.property).symm

def positiveChild : ChildSelection matchingOrderSource where
  species := {0}
  reactions := {0}
  assign := chooseReactionZero
  reactant_match := by intro x; simp [matchingOrderSource, SourceNetwork.toReactionNetwork]

def negativeChild : ChildSelection matchingOrderSource where
  species := {0}
  reactions := {1}
  assign := chooseReactionOne
  reactant_match := by intro x; simp [matchingOrderSource, SourceNetwork.toReactionNetwork]

def selectedSpecies :
    {s // s ∈ ({0} : Finset OneSpecies)} := ⟨0, by simp⟩

/-- Reactant support alone does not determine the child matrix: the selected
reaction assignment and its induced column order are essential data. -/
theorem support_matching_order_regression :
    positiveChild.species = negativeChild.species ∧
      positiveChild.matrix selectedSpecies selectedSpecies = 1 ∧
      negativeChild.matrix selectedSpecies selectedSpecies = -1 := by
  constructor
  · rfl
  constructor
  · change ((if (0 : TwoReactions) = 0 then (2 : ℤ) else 0) - 1) = 1
    norm_num
  · change ((if (1 : TwoReactions) = 0 then (2 : ℤ) else 0) - 1) = -1
    norm_num

end Regression

end DUnstableCores

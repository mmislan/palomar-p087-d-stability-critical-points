module

public import proofs.DUnstableCores.HopfSupport
public import proofs.CoreInteraction.Incidence

@[expose] public section

/-!
# Narrow Core-Interaction-Calculus adapter

This file imports only CIC reaction ownership, literal source reconstruction,
typed factor--species incidence, and private/interface semantics.  It does not
identify reaction factors with child selections and makes no D-stability
composition claim.
-/

namespace DUnstableCores

namespace SourceNetwork

variable {Species Reaction Factor : Type}

/-- Preserve the full literal input, output, and catalyst multiplicities. -/
def toCICSource (Q : SourceNetwork Species Reaction) :
    CoreInteraction.SourceNetwork Species Reaction where
  input := fun s r => Q.reactant s r
  output := fun s r => Q.product s r
  catalyst := fun s r => Q.catalyst s r

/-- Canonical support of an owned factor: no source incidence is inferred from
the net stoichiometric column. -/
def cicOwnedSupport (Q : SourceNetwork Species Reaction)
    (owner : Reaction → Factor) (f : Factor) (s : Species) : Prop :=
  ∃ r : Reaction, owner r = f ∧
    (Q.reactant s r ≠ 0 ∨ Q.product s r ≠ 0 ∨ Q.catalyst s r ≠ 0)

/-- Every reaction has exactly one owner; factor support retains every literal
source incidence.  Core decorations are deliberately absent from this narrow
adapter. -/
noncomputable def toCICFactorization [Fintype Reaction] [DecidableEq Factor]
    (Q : SourceNetwork Species Reaction) (owner : Reaction → Factor) :
    CoreInteraction.Factorization Q.toCICSource Factor PUnit where
  owner := owner
  support := Q.cicOwnedSupport owner
  support_decidable := by
    classical
    exact fun _ _ => inferInstance
  support_complete := by
    intro f s r hown hsource
    refine ⟨r, hown, ?_⟩
    simpa [toCICSource] using hsource
  coreDecorations := fun _ => ∅

variable [Fintype Species] [Fintype Reaction] [Fintype Factor]
variable [DecidableEq Species] [DecidableEq Factor]

/-- The deliberately narrow portion of the CIC source contract imported by
the D-core campaign. -/
def CICSourceContract (Q : SourceNetwork Species Reaction)
    (fac : CoreInteraction.Factorization Q.toCICSource Factor PUnit) : Prop :=
  (∀ s r, ∑ f : Factor, fac.factorInput f s r = Q.toCICSource.input s r) ∧
  (∀ s r, ∑ f : Factor, fac.factorOutput f s r = Q.toCICSource.output s r) ∧
  (∀ s r, ∑ f : Factor, fac.factorCatalyst f s r = Q.toCICSource.catalyst s r) ∧
  (∀ q x s, ∑ f : Factor, fac.residual q x f s =
    CoreInteraction.Factorization.globalResidual Q.toCICSource q x s) ∧
  (∀ f s, fac.incidenceGraph.Adj (Sum.inl f) (Sum.inr s) ↔ fac.support f s) ∧
  (∀ f s, fac.support f s → fac.IsPrivate f s ∨ fac.IsInterface s)

omit [Fintype Species] [DecidableEq Species] in
/-- Exact imported CIC source contract on the translated D-core source. -/
theorem cicFactorization_reconstructs (Q : SourceNetwork Species Reaction)
    (owner : Reaction → Factor) :
    Q.CICSourceContract (Q.toCICFactorization owner) := by
  exact CoreInteraction.Factorization.sourceFaithfulFactorization_reconstructs
    (Q.toCICFactorization owner)

omit [Fintype Species] [Fintype Factor] [DecidableEq Species] in
theorem cic_support_of_reactant (Q : SourceNetwork Species Reaction)
    (owner : Reaction → Factor) {s : Species} {q : Reaction}
    (h : Q.Reactant s q) :
    (Q.toCICFactorization owner).support (owner q) s := by
  exact ⟨q, rfl, Or.inl (Nat.ne_of_gt h)⟩

omit [Fintype Species] [Fintype Factor] [DecidableEq Species] in
theorem cic_support_of_stoich_ne (Q : SourceNetwork Species Reaction)
    (owner : Reaction → Factor) {s : Species} {q : Reaction}
    (h : (Q.stoich s q : ℝ) ≠ 0) :
    (Q.toCICFactorization owner).support (owner q) s := by
  have heither : Q.reactant s q ≠ 0 ∨ Q.product s q ≠ 0 := by
    by_contra hnone
    push Not at hnone
    apply h
    simp [SourceNetwork.stoich, hnone.1, hnone.2]
  exact ⟨q, rfl, heither.elim Or.inl (fun hp => Or.inr (Or.inl hp))⟩

end SourceNetwork

/-- A compact, declaration-probe-friendly statement that every moved edge of
a permutation is carried by one reaction owner's typed CIC incidence. -/
def HasOwnedIncidenceEdges
    {Species Reaction Factor : Type}
    [Fintype Reaction] [DecidableEq Factor]
    (Q : SourceNetwork Species Reaction) (owner : Reaction → Factor)
    (tau : Equiv.Perm Species) : Prop :=
  ∀ i, tau i ≠ i → ∃ q : Reaction,
    (Q.toCICFactorization owner).support (owner q) i ∧
    (Q.toCICFactorization owner).support (owner q) (tau i)

/-- Literal reaction witnesses for the moved edges of a permutation induce
owned factor--species incidence on both endpoints. -/
theorem literal_cycle_edges_have_owned_incidence
    {Species Reaction Factor : Type}
    [Fintype Reaction] [DecidableEq Factor]
    (Q : SourceNetwork Species Reaction) (owner : Reaction → Factor)
    (tau : Equiv.Perm Species)
    (hedges : ∀ i, tau i ≠ i → ∃ q : Reaction,
      Q.Reactant i q ∧ (Q.stoich (tau i) q : ℝ) ≠ 0) :
    HasOwnedIncidenceEdges Q owner tau := by
  intro i hi
  obtain ⟨q, hreact, hstoich⟩ := hedges i hi
  exact ⟨q, Q.cic_support_of_reactant owner hreact,
    Q.cic_support_of_stoich_ne owner hstoich⟩

/--
Every edge of the minimal Hurwitz cycle is a two-sided typed incidence through
the owner of its literal witnessing reaction.  This is the narrow bridge from
the Hopf certificate to CIC; it does not collapse reaction ownership into a
child-selection assignment.
-/
theorem minimal_hurwitz_circuit_has_owned_incidence_edges
    {Species Reaction Factor : Type}
    [Fintype Species] [DecidableEq Species]
    [Fintype Reaction] [Fintype Factor] [DecidableEq Factor]
    {Q : SourceNetwork Species Reaction} {R : Reactivity Q} {lam : ℂ}
    (C : MinimalHurwitzInteractionCircuit Q R lam)
    (owner : Reaction → Factor) :
    HasOwnedIncidenceEdges Q owner C.cycle := by
  exact literal_cycle_edges_have_owned_incidence Q owner C.cycle C.literal_edges

end DUnstableCores

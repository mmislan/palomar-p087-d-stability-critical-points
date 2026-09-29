module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import proofs.CoreInteraction.Source

@[expose] public section

/-! Typed factor--species incidence for a certified reaction factorization. -/

namespace CoreInteraction

variable {Species Reaction Factor CoreId : Type}
variable [Fintype Species] [Fintype Reaction] [Fintype Factor]
variable [DecidableEq Species] [DecidableEq Factor]
variable {Q : SourceNetwork Species Reaction}

namespace Factorization

def IsInterface (fac : Factorization Q Factor CoreId) (s : Species) : Prop :=
  ∃ f g : Factor, f ≠ g ∧ fac.support f s ∧ fac.support g s

def IsPrivate (fac : Factorization Q Factor CoreId) (f : Factor) (s : Species) : Prop :=
  fac.support f s ∧ ∀ g, fac.support g s → g = f

def incidenceRel (fac : Factorization Q Factor CoreId) :
    (Factor ⊕ Species) → (Factor ⊕ Species) → Prop
  | Sum.inl f, Sum.inr s => fac.support f s
  | Sum.inr s, Sum.inl f => fac.support f s
  | _, _ => False

def incidenceGraph (fac : Factorization Q Factor CoreId) :
    SimpleGraph (Factor ⊕ Species) :=
  SimpleGraph.fromRel fac.incidenceRel

omit [Fintype Species] [Fintype Reaction] [Fintype Factor]
    [DecidableEq Species] [DecidableEq Factor] in
@[simp] theorem incidenceGraph_adj_factor_species
    (fac : Factorization Q Factor CoreId) (f : Factor) (s : Species) :
    fac.incidenceGraph.Adj (Sum.inl f) (Sum.inr s) ↔ fac.support f s := by
  simp [incidenceGraph, SimpleGraph.fromRel_adj, incidenceRel]

omit [Fintype Species] [Fintype Reaction] [Fintype Factor]
    [DecidableEq Species] [DecidableEq Factor] in
@[simp] theorem incidenceGraph_adj_species_factor
    (fac : Factorization Q Factor CoreId) (s : Species) (f : Factor) :
    fac.incidenceGraph.Adj (Sum.inr s) (Sum.inl f) ↔ fac.support f s := by
  simp [incidenceGraph, SimpleGraph.fromRel_adj, incidenceRel]

def IncidenceForest (fac : Factorization Q Factor CoreId) : Prop :=
  fac.incidenceGraph.IsAcyclic

omit [Fintype Species] [Fintype Reaction] [Fintype Factor]
    [DecidableEq Species] [DecidableEq Factor] in
theorem private_not_interface (fac : Factorization Q Factor CoreId)
    {f : Factor} {s : Species} (hprivate : fac.IsPrivate f s) :
    ¬ fac.IsInterface s := by
  rintro ⟨g, h, gh, hgs, hhs⟩
  have hgf : g = f := hprivate.2 g hgs
  have hhf : h = f := hprivate.2 h hhs
  exact gh (hgf.trans hhf.symm)

omit [Fintype Species] [Fintype Reaction] [DecidableEq Species] in
theorem support_private_or_interface (fac : Factorization Q Factor CoreId)
    {f : Factor} {s : Species} (hfs : fac.support f s) :
    fac.IsPrivate f s ∨ fac.IsInterface s := by
  by_cases hprivate : ∀ g, fac.support g s → g = f
  · exact Or.inl ⟨hfs, hprivate⟩
  · rw [not_forall] at hprivate
    obtain ⟨g, hg⟩ := hprivate
    have hgs : fac.support g s := by
      by_contra hnot
      exact hg (fun h => False.elim (hnot h))
    have hgf : g ≠ f := by
      intro heq
      exact hg (fun _ => heq)
    exact Or.inr ⟨f, g, hgf.symm, hfs, hgs⟩

omit [Fintype Species] [DecidableEq Species] in
/-- Public `CIC-SOURCE` interface: ownership reconstructs all literal source
matrices and residuals, while graph adjacency is exactly typed support
incidence and every supported species is private or shared. -/
theorem sourceFaithfulFactorization_reconstructs
    (fac : Factorization Q Factor CoreId) :
    (∀ s r, ∑ f : Factor, fac.factorInput f s r = Q.input s r) ∧
    (∀ s r, ∑ f : Factor, fac.factorOutput f s r = Q.output s r) ∧
    (∀ s r, ∑ f : Factor, fac.factorCatalyst f s r = Q.catalyst s r) ∧
    (∀ q x s, ∑ f : Factor, fac.residual q x f s = globalResidual Q q x s) ∧
    (∀ f s, fac.incidenceGraph.Adj (Sum.inl f) (Sum.inr s) ↔ fac.support f s) ∧
    (∀ f s, fac.support f s → fac.IsPrivate f s ∨ fac.IsInterface s) := by
  exact ⟨fac.sum_factorInput, fac.sum_factorOutput, fac.sum_factorCatalyst,
    fac.residual_sum_eq_global, fac.incidenceGraph_adj_factor_species,
    fun _ _ h => fac.support_private_or_interface h⟩

end Factorization

end CoreInteraction

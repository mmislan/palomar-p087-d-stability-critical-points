module

public import proofs.DUnstableCores.HopfStar

@[expose] public section

/-!
# Determinant extraction of a phase-carrying permutation circuit

At a genuinely nonreal characteristic root, every diagonal factor of
`λI - A` is nonzero.  Since the determinant vanishes, a nonidentity Leibniz
term must cancel the identity term.  Its moved coordinates give a directed
cycle cover made only of nonzero entries of `A`.
-/

namespace DUnstableCores

open scoped BigOperators ComplexConjugate

def HasPermutationInteractionCircuit
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : Prop :=
  ∃ σ : Equiv.Perm ι, σ ≠ 1 ∧
    ∀ i, σ i ≠ i → A (σ i) i ≠ 0

theorem exists_nonidentity_permutation_term_of_det_zero
    {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [Field K] (M : Matrix ι ι K)
    (hdet : Matrix.det M = 0) (hdiag : ∀ i, M i i ≠ 0) :
    ∃ σ : Equiv.Perm ι, σ ≠ 1 ∧
      (∏ i, M (σ i) i) ≠ 0 := by
  by_contra hnone
  push Not at hnone
  have hcollapse : Matrix.det M = ∏ i, M i i := by
    rw [Matrix.det_apply']
    calc
      (∑ σ : Equiv.Perm ι,
          ((Equiv.Perm.sign σ : ℤ) : K) * ∏ i, M (σ i) i) =
          ∑ σ : Equiv.Perm ι,
            if σ = 1 then ∏ i, M i i else 0 := by
        apply Finset.sum_congr rfl
        intro σ _
        by_cases hσ : σ = 1
        · subst σ
          simp
        · have hp := hnone σ hσ
          simp [hσ, hp]
      _ = ∏ i, M i i := by simp
  have hprod : (∏ i, M i i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => hdiag i
  apply hprod
  rw [← hcollapse, hdet]

theorem nonreal_charpoly_root_yields_permutation_interaction_circuit
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (lam : ℂ)
    (hroot : (complexify A).charpoly.IsRoot lam) (himne : lam.im ≠ 0) :
    HasPermutationInteractionCircuit A := by
  let M : Matrix ι ι ℂ := Matrix.scalar ι lam - complexify A
  have hdet : Matrix.det M = 0 := by
    have heval : (complexify A).charpoly.eval lam = 0 := hroot
    rw [Matrix.eval_charpoly] at heval
    exact heval
  have hdiag : ∀ i, M i i ≠ 0 := by
    intro i hzero
    have him := congrArg Complex.im hzero
    simp [M, Matrix.scalar_apply, complexify] at him
    exact himne him
  obtain ⟨σ, hσ, hterm⟩ :=
    exists_nonidentity_permutation_term_of_det_zero M hdet hdiag
  refine ⟨σ, hσ, ?_⟩
  intro i hi
  have hfactor : M (σ i) i ≠ 0 := by
    intro hzero
    apply hterm
    exact Finset.prod_eq_zero (Finset.mem_univ i) hzero
  intro hA
  apply hfactor
  simp [M, Matrix.scalar_apply, hi, complexify, hA]

/-- A nonzero Jacobian entry has an explicit nonzero literal reaction term. -/
theorem nonzero_jacobian_entry_localizes_to_reaction
    {Species Reaction : Type*} [Fintype Reaction]
    (Q : SourceNetwork Species Reaction) (R : Reactivity Q) (i j : Species)
    (hentry : Q.jacobian R i j ≠ 0) :
    ∃ q : Reaction, Q.Reactant j q ∧ (Q.stoich i q : ℝ) ≠ 0 := by
  by_contra hnone
  push Not at hnone
  apply hentry
  rw [Q.jacobian_apply R i j]
  apply Finset.sum_eq_zero
  intro q _
  by_cases hreact : Q.Reactant j q
  · rw [hnone q hreact]
    simp
  · rw [R.zero_of_not_reactant q j hreact]
    simp

/--
An uncompressed source-level permutation circuit: every moved species column
chooses a literal reactant reaction whose stoichiometric edge to the next
species is nonzero.
-/
def HasLiteralPermutationInteractionCircuit
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    (Q : SourceNetwork Species Reaction) : Prop :=
  ∃ σ : Equiv.Perm Species, σ ≠ 1 ∧
    ∀ i, σ i ≠ i →
      ∃ q : Reaction, Q.Reactant i q ∧ (Q.stoich (σ i) q : ℝ) ≠ 0

/--
Every genuinely nonreal source-Jacobian characteristic root produces an
authenticated literal reaction interaction circuit, with no support
compression and no support-minimality assumption.
-/
theorem nonreal_source_charpoly_root_yields_literal_permutation_circuit
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    [Fintype Reaction]
    (Q : SourceNetwork Species Reaction) (R : Reactivity Q) (lam : ℂ)
    (hroot : (complexify (Q.jacobian R)).charpoly.IsRoot lam)
    (himne : lam.im ≠ 0) :
    HasLiteralPermutationInteractionCircuit Q := by
  obtain ⟨σ, hσ, hedge⟩ :=
    nonreal_charpoly_root_yields_permutation_interaction_circuit
      (Q.jacobian R) lam hroot himne
  refine ⟨σ, hσ, ?_⟩
  intro i hi
  exact nonzero_jacobian_entry_localizes_to_reaction
    Q R (σ i) i (hedge i hi)

/-- A single literal reaction cycle rather than a possibly disconnected cover. -/
def HasLiteralCycleInteractionCircuit
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    (Q : SourceNetwork Species Reaction) : Prop :=
  ∃ τ : Equiv.Perm Species, τ.IsCycle ∧
    ∀ i, τ i ≠ i →
      ∃ q : Reaction, Q.Reactant i q ∧ (Q.stoich (τ i) q : ℝ) ≠ 0

theorem literal_permutation_circuit_contains_literal_cycle
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    {Q : SourceNetwork Species Reaction}
    (h : HasLiteralPermutationInteractionCircuit Q) :
    HasLiteralCycleInteractionCircuit Q := by
  obtain ⟨σ, hσ, hedge⟩ := h
  have hmoved : ∃ x : Species, σ x ≠ x := by
    by_contra hfixed
    push Not at hfixed
    apply hσ
    ext x
    exact hfixed x
  obtain ⟨x, hx⟩ := hmoved
  let τ : Equiv.Perm Species := σ.cycleOf x
  have hτ : τ.IsCycle := by
    exact Equiv.Perm.isCycle_cycleOf σ hx
  refine ⟨τ, hτ, ?_⟩
  intro i hi
  have himem : i ∈ τ.support := Equiv.Perm.mem_support.mpr hi
  have hsame : σ.SameCycle x i := by
    exact (Equiv.Perm.mem_support_cycleOf_iff' hx).mp himem
  have heq : τ i = σ i := by
    exact hsame.cycleOf_apply
  have hσi : σ i ≠ i := by
    rwa [← heq]
  obtain ⟨q, hreact, hstoich⟩ := hedge i hσi
  exact ⟨q, hreact, by simpa [heq] using hstoich⟩

/--
The arbitrary finite source-faithful Hopf-support conclusion: a genuinely
nonreal characteristic root exposes one literal phase-carrying interaction
cycle.  No support compression or prior minimality choice is needed.
-/
theorem nonreal_source_charpoly_root_yields_literal_cycle
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    [Fintype Reaction]
    (Q : SourceNetwork Species Reaction) (R : Reactivity Q) (lam : ℂ)
    (hroot : (complexify (Q.jacobian R)).charpoly.IsRoot lam)
    (himne : lam.im ≠ 0) :
    HasLiteralCycleInteractionCircuit Q := by
  exact literal_permutation_circuit_contains_literal_cycle
    (nonreal_source_charpoly_root_yields_literal_permutation_circuit
      Q R lam hroot himne)

end DUnstableCores

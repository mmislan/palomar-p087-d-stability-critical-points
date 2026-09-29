module

public import proofs.DUnstableCores.HopfPermutationCircuit

@[expose] public section

/-!
# Public Hopf-support interface

This module packages the arbitrary finite source-faithful interaction-cycle
extraction behind the exact imaginary-eigenpair interface used by the active
campaign node.
-/

namespace DUnstableCores

open scoped BigOperators

/--
An exact phase-carrying interaction certificate at a nonreal characteristic
root.  Besides the literal source cycle, it retains the two determinant terms
whose cancellation cannot be seen from static principal-minor signs: the
nonzero identity term and a nonzero nonidentity permutation-cover term.  The
selected `cycle` is one genuine cycle of that cover, hence is combinatorially
minimal rather than a disconnected cycle cover.
-/
structure MinimalHurwitzInteractionCircuit
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    [Fintype Reaction]
    (Q : SourceNetwork Species Reaction) (R : Reactivity Q) (lam : ℂ) where
  nonreal : lam.im ≠ 0
  charpolyRoot : (complexify (Q.jacobian R)).charpoly.IsRoot lam
  cover : Equiv.Perm Species
  cover_nonidentity : cover ≠ 1
  determinant_zero :
    Matrix.det (Matrix.scalar Species lam - complexify (Q.jacobian R)) = 0
  identity_term_nonzero :
    (∏ i, (Matrix.scalar Species lam - complexify (Q.jacobian R)) i i) ≠ 0
  cover_term_nonzero :
    (∏ i, (Matrix.scalar Species lam - complexify (Q.jacobian R)) (cover i) i) ≠ 0
  cycle : Equiv.Perm Species
  cycle_isCycle : cycle.IsCycle
  cycle_of_cover : ∃ x, cover x ≠ x ∧ cycle = cover.cycleOf x
  literal_edges : ∀ i, cycle i ≠ i →
    ∃ q : Reaction, Q.Reactant i q ∧ (Q.stoich (cycle i) q : ℝ) ≠ 0

theorem nonreal_source_root_yields_minimal_hurwitz_circuit
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    [Fintype Reaction]
    (Q : SourceNetwork Species Reaction) (R : Reactivity Q) (lam : ℂ)
    (hroot : (complexify (Q.jacobian R)).charpoly.IsRoot lam)
    (himne : lam.im ≠ 0) :
    Nonempty (MinimalHurwitzInteractionCircuit Q R lam) := by
  let M : Matrix Species Species ℂ :=
    Matrix.scalar Species lam - complexify (Q.jacobian R)
  have hdet : Matrix.det M = 0 := by
    have heval : (complexify (Q.jacobian R)).charpoly.eval lam = 0 := hroot
    rw [Matrix.eval_charpoly] at heval
    exact heval
  have hdiag : ∀ i, M i i ≠ 0 := by
    intro i hzero
    have him := congrArg Complex.im hzero
    simp [M, Matrix.scalar_apply, complexify] at him
    exact himne him
  obtain ⟨σ, hσ, hterm⟩ :=
    exists_nonidentity_permutation_term_of_det_zero M hdet hdiag
  have hmoved : ∃ x : Species, σ x ≠ x := by
    by_contra hfixed
    push Not at hfixed
    apply hσ
    ext x
    exact hfixed x
  obtain ⟨x, hx⟩ := hmoved
  let τ : Equiv.Perm Species := σ.cycleOf x
  constructor
  refine
    { nonreal := himne
      charpolyRoot := hroot
      cover := σ
      cover_nonidentity := hσ
      determinant_zero := by simpa [M] using hdet
      identity_term_nonzero := by
        simpa [M] using (Finset.prod_ne_zero_iff.mpr fun i _ => hdiag i)
      cover_term_nonzero := by simpa [M] using hterm
      cycle := τ
      cycle_isCycle := Equiv.Perm.isCycle_cycleOf σ hx
      cycle_of_cover := ⟨x, hx, rfl⟩
      literal_edges := ?_ }
  intro i hi
  have himem : i ∈ τ.support := Equiv.Perm.mem_support.mpr hi
  have hsame : σ.SameCycle x i := by
    exact (Equiv.Perm.mem_support_cycleOf_iff' hx).mp himem
  have heq : τ i = σ i := hsame.cycleOf_apply
  have hσi : σ i ≠ i := by rwa [← heq]
  have hfactor : M (σ i) i ≠ 0 := by
    intro hzero
    apply hterm
    exact Finset.prod_eq_zero (Finset.mem_univ i) hzero
  have hentry : Q.jacobian R (σ i) i ≠ 0 := by
    intro hzero
    apply hfactor
    simp [M, Matrix.scalar_apply, hσi, complexify, hzero]
  obtain ⟨q, hreact, hstoich⟩ :=
    nonzero_jacobian_entry_localizes_to_reaction Q R (σ i) i hentry
  exact ⟨q, hreact, by simpa [heq] using hstoich⟩

theorem imaginary_eigenpair_yields_literal_cycle
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    [Fintype Reaction]
    (Q : SourceNetwork Species Reaction) (R : Reactivity Q)
    (omega : ℝ) (z : Species → ℂ) (homega : 0 < omega)
    (hpair : HasEigenpair (Q.jacobian R)
      ((omega : ℂ) * Complex.I) z) :
    HasLiteralCycleInteractionCircuit Q := by
  apply nonreal_source_charpoly_root_yields_literal_cycle
    Q R ((omega : ℂ) * Complex.I)
  · exact hpair.isRoot_charpoly
  · simpa using homega.ne'

/--
The exact active-node disjunction.  The conclusion is stronger than required:
the literal interaction-cycle arm always holds, without first minimizing the
reactant support.
-/
theorem imaginary_eigenpair_yields_core_or_literal_cycle
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    [DecidableEq Reaction] [Fintype Reaction]
    (Q : SourceNetwork Species Reaction) (R : Reactivity Q)
    (omega : ℝ) (z : Species → ℂ) (homega : 0 < omega)
    (hpair : HasEigenpair (Q.jacobian R)
      ((omega : ℂ) * Complex.I) z) :
    (∃ core : ChildSelection Q, IsDUnstableCore core) ∨
      HasLiteralCycleInteractionCircuit Q := by
  exact Or.inr (imaginary_eigenpair_yields_literal_cycle
    Q R omega z homega hpair)

/--
The typed adapter requested by the active Hopf-support node.  No separate
support-minimality hypothesis is needed: every imaginary eigenpair already
produces a single-cycle, source-faithful determinant-cancellation certificate.
-/
theorem imaginary_eigenpair_yields_core_or_minimal_hurwitz_circuit
    {Species Reaction : Type*} [Fintype Species] [DecidableEq Species]
    [DecidableEq Reaction] [Fintype Reaction]
    (Q : SourceNetwork Species Reaction) (R : Reactivity Q)
    (omega : ℝ) (z : Species → ℂ) (homega : 0 < omega)
    (hpair : HasEigenpair (Q.jacobian R)
      ((omega : ℂ) * Complex.I) z) :
    (∃ core : ChildSelection Q, IsDUnstableCore core) ∨
      Nonempty (MinimalHurwitzInteractionCircuit Q R
        ((omega : ℂ) * Complex.I)) := by
  right
  apply nonreal_source_root_yields_minimal_hurwitz_circuit Q R
  · exact hpair.isRoot_charpoly
  · simpa using homega.ne'

theorem hopfSource4_has_literal_cycle :
    HasLiteralCycleInteractionCircuit hopfSource4 := by
  apply imaginary_eigenpair_yields_literal_cycle
    hopfSource4 hopfReactivity4 1 hopfRight4 (by norm_num)
  rw [hopfSource4_jacobian]
  simpa using hopfCompanion4_right_eigenpair

end DUnstableCores

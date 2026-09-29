module

public import proofs.DUnstableCores.HopfSourceLift

@[expose] public section

/-!
# Exact phase localization on a diagonal-branch star

For mutually uncoupled branch vertices, every branch message has a strictly
positive denominator `bᵢ² + ω²`.  The root imaginary equation therefore
forces at least one oppositely signed two-cycle.
-/

namespace DUnstableCores

open scoped BigOperators

theorem HopfBranchSolveWitness.exists_negative_two_cycle_of_diagonal_branch
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a ω : ℝ} {r c b : ι → ℝ} {B : Matrix ι ι ℝ}
    (w : HopfBranchSolveWitness a r c B ω) (hω : 0 < ω)
    (hB : ∀ i j, B i j = if i = j then b i else 0) :
    ∃ i : ι, r i * c i < 0 := by
  by_contra hnone
  push Not at hnone
  have hrv : ∀ i : ι, r i * w.v i ≤ 0 := by
    intro i
    have hreal : -b i * w.u i - ω * w.v i = c i := by
      have h := w.branch_real i
      simpa [Matrix.mulVec, dotProduct, hB] using h
    have himag : ω * w.u i - b i * w.v i = 0 := by
      have h := w.branch_imag i
      simpa [Matrix.mulVec, dotProduct, hB] using h
    have hv : (b i ^ 2 + ω ^ 2) * w.v i + ω * c i = 0 := by
      linear_combination -b i * himag - ω * hreal
    have hweighted :
        (b i ^ 2 + ω ^ 2) * (r i * w.v i) +
          ω * (r i * c i) = 0 := by
      linear_combination r i * hv
    have hcost : 0 < b i ^ 2 + ω ^ 2 := by
      nlinarith [sq_nonneg (b i), sq_pos_of_pos hω]
    by_contra hpos
    have hrvpos : 0 < r i * w.v i := lt_of_not_ge hpos
    have hfirst : 0 < (b i ^ 2 + ω ^ 2) * (r i * w.v i) :=
      mul_pos hcost hrvpos
    have hsecond : 0 ≤ ω * (r i * c i) :=
      mul_nonneg hω.le (hnone i)
    linarith
  have hsum : dotProduct r w.v ≤ 0 := by
    exact Finset.sum_nonpos fun i _ => hrv i
  have hroot := w.root_imag
  linarith

/--
Source-faithful star corollary: if all non-root branch interactions are
diagonal, a simple imaginary pair exposes a literal opposite-sign reaction
circuit between the root and one branch species.
-/
theorem diagonal_star_hopf_yields_literal_circuit
    {Species Reaction Branch : Type*} [Fintype Reaction]
    [Fintype Branch] [DecidableEq Branch]
    (Q : SourceNetwork Species Reaction) (R : Reactivity Q)
    (root : Species) (branch : Branch → Species)
    (bdiag : Branch → ℝ) (ω : ℝ)
    (w : HopfBranchSolveWitness (Q.jacobian R root root)
      (fun i => Q.jacobian R root (branch i))
      (fun i => Q.jacobian R (branch i) root)
      (fun i j => Q.jacobian R (branch i) (branch j)) ω)
    (hω : 0 < ω)
    (hB : ∀ i j, Q.jacobian R (branch i) (branch j) =
      if i = j then bdiag i else 0) :
    ∃ i : Branch, HasLiteralOppositeSignCircuit Q root (branch i) := by
  obtain ⟨i, hi⟩ := w.exists_negative_two_cycle_of_diagonal_branch hω hB
  exact ⟨i, negative_jacobian_two_cycle_yields_literal_circuit
    Q R root (branch i) hi⟩

end DUnstableCores

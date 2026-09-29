module

public import proofs.DUnstableCores.Certificates
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix

@[expose] public section

/-!
# Exact characteristic-polynomial interface

Coefficient acceptance is exact: the characteristic polynomial is Mathlib's
determinantal polynomial, not a floating-point list of approximate roots.
-/

namespace DUnstableCores

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Coefficient `k` of the exact characteristic polynomial. -/
noncomputable def characteristicCoefficient (A : Matrix ι ι ℝ) (k : ℕ) : ℝ :=
  A.charpoly.coeff k

theorem characteristicCoefficient_spec (A : Matrix ι ι ℝ) (k : ℕ) :
    characteristicCoefficient A k = A.charpoly.coeff k := rfl

/-- In dimension two the exact coefficient vector is
`(det A, -trace A, 1)`. -/
theorem charpoly_fin_two_exact (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A.charpoly = Polynomial.X ^ 2 - Polynomial.C A.trace * Polynomial.X +
      Polynomial.C A.det :=
  Matrix.charpoly_fin_two A

@[simp] theorem characteristicCoefficient_fin_two_zero
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    characteristicCoefficient A 0 = A.det := by
  rw [characteristicCoefficient, charpoly_fin_two_exact]
  simp

@[simp] theorem characteristicCoefficient_fin_two_one
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    characteristicCoefficient A 1 = -A.trace := by
  rw [characteristicCoefficient, charpoly_fin_two_exact]
  simp

@[simp] theorem characteristicCoefficient_fin_two_two
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    characteristicCoefficient A 2 = 1 := by
  rw [characteristicCoefficient, charpoly_fin_two_exact]
  simp

/-- The campaign's direct eigenpair predicate implies the exact determinant
characteristic polynomial vanishes. -/
theorem HasEigenpair.isRoot_charpoly {A : Matrix ι ι ℝ} {lam : ℂ}
    {v : ι → ℂ} (h : HasEigenpair A lam v) :
    (complexify A).charpoly.IsRoot lam := by
  classical
  let f : Module.End ℂ (ι → ℂ) := (complexify A).mulVecLin
  have hev : Module.End.HasEigenvector f lam v := by
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, h.1⟩
    funext i
    simpa [f, Matrix.mulVecLin_apply] using h.2 i
  have heval : Module.End.HasEigenvalue f lam :=
    Module.End.hasEigenvalue_of_hasEigenvector hev
  have hroot :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly f lam).mp heval
  simpa [f, Matrix.charpoly_mulVecLin] using hroot

end DUnstableCores

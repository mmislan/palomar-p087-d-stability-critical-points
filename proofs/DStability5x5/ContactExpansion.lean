module

public import proofs.DStability5x5.MorseCoverage

@[expose] public section

/-!
# Principal-minor expansion of Johnson's contact determinant (all n)

`contactDet A d = det (i • 1 - A · diag d)` expands, by multilinearity of the determinant in the
columns, as

  `contactDet A d = ∑ S, i ^ (n - |S|) * (∏ l ∈ S, d l) * pminor A S`,

where `pminor A S` is the principal minor `det (-A)[S]`, realised as the determinant of the
`n × n` matrix whose row `l` is column `l` of `-A` for `l ∈ S` and the unit row `e_l` otherwise
(`pminorMat`).  This is the explicit multiaffine polynomial used by the computational criterion:
its real and imaginary parts are `P_re` and `P_im` of THEOREM_5x5.md.
-/

noncomputable section

open Matrix Finset

namespace DStability5x5

open DUnstableCores

variable {n : ℕ}

/-- Transposed principal-minor matrix: row `l` is column `l` of `-A` if `l ∈ S`, else `e_l`. -/
def pminorMat (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) : Matrix (Fin n) (Fin n) ℂ :=
  fun l k => if l ∈ S then ((-A k l : ℝ) : ℂ) else (if l = k then 1 else 0)

/-- The principal minor `det (-A)[S]` (as a complex number). -/
def pminor (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) : ℂ := (pminorMat A S).det

theorem contactDet_expansion (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) :
    contactDet A d = ∑ S : Finset (Fin n),
      Complex.I ^ (n - S.card) * (∏ l ∈ S, (d l : ℂ)) * pminor A S := by
  classical
  unfold contactDet
  rw [← Matrix.det_transpose]
  -- rows of the transpose: row l = (d l) • (column l of -A) + I • e_l
  let colNeg : Fin n → Fin n → ℂ := fun l k => ((-A k l : ℝ) : ℂ)
  let unit : Fin n → Fin n → ℂ := fun l k => if l = k then 1 else 0
  have hrows : (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ) - complexify (rightScale A d))ᵀ =
      (fun l => (fun l => ((d l : ℝ) : ℂ) • colNeg l) l + (fun l => Complex.I • unit l) l) := by
    funext l k
    simp only [Matrix.transpose_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      complexify, rightScale, colNeg, unit, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases h : l = k
    · subst h
      simp
      ring
    · have h' : k ≠ l := fun e => h e.symm
      simp [h, h']
      ring
  have hdet : ∀ M : Matrix (Fin n) (Fin n) ℂ, M.det = Matrix.detRowAlternating M := fun _ => rfl
  rw [hdet, hrows]
  have hadd := (Matrix.detRowAlternating : (Fin n → ℂ) [⋀^Fin n]→ₗ[ℂ] ℂ).toMultilinearMap.map_add_univ
    (fun l => ((d l : ℝ) : ℂ) • colNeg l) (fun l => Complex.I • unit l)
  simp only [AlternatingMap.coe_multilinearMap] at hadd
  rw [show (fun l => ((d l : ℝ) : ℂ) • colNeg l) + (fun l => Complex.I • unit l) =
      (fun l => (fun l => ((d l : ℝ) : ℂ) • colNeg l) l + (fun l => Complex.I • unit l) l) from rfl] at hadd
  rw [hadd]
  refine Finset.sum_congr rfl fun S _ => ?_
  -- the piecewise family is a coordinatewise smul
  have hpw : S.piecewise (fun l => ((d l : ℝ) : ℂ) • colNeg l) (fun l => Complex.I • unit l) =
      fun l => (if l ∈ S then ((d l : ℝ) : ℂ) else Complex.I) • (pminorMat A S l) := by
    funext l
    by_cases hl : l ∈ S
    · simp only [Finset.piecewise, hl, ite_true]
      funext k
      simp [pminorMat, hl, colNeg]
    · simp only [Finset.piecewise, hl, ite_false]
      funext k
      simp [pminorMat, hl, unit]
  rw [hpw]
  have hsmul := (Matrix.detRowAlternating : (Fin n → ℂ) [⋀^Fin n]→ₗ[ℂ] ℂ).toMultilinearMap.map_smul_univ
    (fun l => if l ∈ S then ((d l : ℝ) : ℂ) else Complex.I) (fun l => pminorMat A S l)
  simp only [AlternatingMap.coe_multilinearMap] at hsmul
  rw [hsmul, smul_eq_mul]
  have hprod : (∏ l, (if l ∈ S then ((d l : ℝ) : ℂ) else Complex.I)) =
      Complex.I ^ (n - S.card) * ∏ l ∈ S, (d l : ℂ) := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const]
    have hc : (Finset.univ.filter fun l => l ∉ S).card = n - S.card := by
      have hS : (Finset.univ.filter fun l => l ∉ S) = Sᶜ := by
        ext l
        simp
      rw [hS, Finset.card_compl, Fintype.card_fin]
    rw [hc, mul_comm]
    congr 1
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [hprod]
  rfl

end DStability5x5

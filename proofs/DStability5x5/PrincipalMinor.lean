module

public import proofs.DStability5x5.ContactExpansion

@[expose] public section

/-!
# The principal-minor coefficients of the contact polynomial are real

`pminor A S` is the determinant of `pminorMat A S`, whose row `l` is column `l` of `-A` for
`l ∈ S` and the unit row `e_l` otherwise.  Its rows outside `S` vanish on the `S`-columns, so the
matrix is block triangular with an identity block, and its determinant is the real principal
minor

  `minorR A S = det ((-A)[S])`

(cast to `ℂ`; the transpose does not change the determinant).  For `S = ∅` this minor is `1`.
-/

noncomputable section

open Matrix Finset

namespace DStability5x5

variable {n : ℕ}

/-- The real principal minor `m_S = det ((-A)[S])`; for `S = ∅` it equals `1`. -/
def minorR (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) : ℝ :=
  ((-A).submatrix (fun i : S => (i : Fin n)) (fun i : S => (i : Fin n))).det

/-- The real matrix underlying `pminorMat`. -/
def pminorMatR (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun l k => if l ∈ S then -A k l else (if l = k then 1 else 0)

theorem pminorMat_eq_map (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) :
    pminorMat A S = (Complex.ofRealHom).mapMatrix (pminorMatR A S) := by
  ext l k
  show pminorMat A S l k = Complex.ofRealHom (pminorMatR A S l k)
  simp only [pminorMat, pminorMatR]
  split_ifs <;> simp

theorem pminorMatR_det (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) :
    (pminorMatR A S).det = minorR A S := by
  have hblock : ∀ i, ¬ (i ∈ S) → ∀ j, j ∈ S → pminorMatR A S i j = 0 := by
    intro i hi j hj
    have hij : i ≠ j := by
      rintro rfl
      exact hi hj
    show (if i ∈ S then -A j i else (if i = j then 1 else 0)) = 0
    rw [ite_eq_right hi, ite_eq_right hij]
  have h2 : toSquareBlockProp (pminorMatR A S) (fun i => ¬ i ∈ S) = 1 := by
    ext a b
    have ha : ¬ (a : Fin n) ∈ S := a.2
    rw [Matrix.one_apply]
    show (if (a : Fin n) ∈ S then -A b a else (if (a : Fin n) = b then 1 else 0)) =
      if a = b then 1 else 0
    rw [ite_eq_right ha]
    by_cases hab : a = b
    · rw [ite_eq_left hab, ite_eq_left (congrArg Subtype.val hab)]
    · rw [ite_eq_right hab, ite_eq_right (fun h => hab (Subtype.ext h))]
  have h1 : toSquareBlockProp (pminorMatR A S) (fun i => i ∈ S) =
      ((-A).submatrix (fun i : S => (i : Fin n)) (fun i : S => (i : Fin n)))ᵀ := by
    ext a b
    have ha : (a : Fin n) ∈ S := a.2
    show (if (a : Fin n) ∈ S then -A b a else (if (a : Fin n) = b then 1 else 0)) = (-A) b a
    rw [ite_eq_left ha, Matrix.neg_apply]
  rw [twoBlockTriangular_det (pminorMatR A S) (fun i => i ∈ S) hblock, h2, det_one, mul_one, h1]
  unfold minorR
  rw [← det_transpose ((-A).submatrix (fun i : S => (i : Fin n)) (fun i : S => (i : Fin n)))]
  congr!

/-- The complex principal minor `pminor A S` is the real principal minor `det ((-A)[S])`. -/
theorem pminor_eq_minorR (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) :
    pminor A S = (minorR A S : ℂ) := by
  rw [pminor, pminorMat_eq_map, ← RingHom.map_det, pminorMatR_det, Complex.ofRealHom_eq_coe]

theorem pminor_im (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) :
    (pminor A S).im = 0 := by
  rw [pminor_eq_minorR]
  exact Complex.ofReal_im _

theorem pminor_re (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) :
    (pminor A S).re = minorR A S := by
  rw [pminor_eq_minorR]
  exact Complex.ofReal_re _

/-- The empty principal minor is `1`. -/
theorem minorR_empty (A : Matrix (Fin n) (Fin n) ℝ) : minorR A ∅ = 1 := by
  have : IsEmpty (↥(∅ : Finset (Fin n))) := ⟨fun x => Finset.notMem_empty x.1 x.2⟩
  exact Matrix.det_isEmpty

end DStability5x5

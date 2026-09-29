module

public import proofs.DUnstableCores.HopfMatching

@[expose] public section

/-!
# Block-triangular instability localization

The off-diagonal coupling of a block-triangular matrix cannot create a new
characteristic root.  The result is stated both for Hurwitz instability and
for positive right-diagonal scaling, the latter being the exact D-instability
operation used by the campaign.
-/

namespace DUnstableCores

theorem complexify_fromBlocks
    {m n : Type*}
    (A : Matrix m m ℝ) (B : Matrix m n ℝ)
    (C : Matrix n m ℝ) (D : Matrix n n ℝ) :
    complexify (Matrix.fromBlocks A B C D) =
      Matrix.fromBlocks (complexify A) (fun i j => (B i j : ℂ))
        (fun i j => (C i j : ℂ)) (complexify D) := by
  ext i j
  cases i <;> cases j <;> rfl

/-- Over a finite complex vector space, every characteristic root has a
nonzero eigenvector in the campaign's direct matrix-vector interface. -/
theorem isRoot_complexified_charpoly_yields_eigenpair
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (lam : ℂ)
    (hroot : (complexify A).charpoly.IsRoot lam) :
    ∃ v : ι → ℂ, HasEigenpair A lam v := by
  classical
  let f : Module.End ℂ (ι → ℂ) := (complexify A).mulVecLin
  have hrootEnd : f.charpoly.IsRoot lam := by
    simpa [f, Matrix.charpoly_mulVecLin] using hroot
  have heigenvalue : Module.End.HasEigenvalue f lam :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly f lam).mpr hrootEnd
  obtain ⟨v, hv⟩ := heigenvalue.exists_hasEigenvector
  refine ⟨v, hv.2, ?_⟩
  intro i
  have happly : f v = lam • v := Module.End.mem_eigenspace_iff.mp hv.1
  have hi := congrFun happly i
  simpa [f, Matrix.mulVecLin_apply] using hi

/-- A characteristic root of an upper block-triangular real matrix belongs to
one of its diagonal blocks. -/
theorem isRoot_fromBlocks_zero21_localizes
    {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n]
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ)
    (lam : ℂ)
    (hroot : (complexify (Matrix.fromBlocks A B 0 D)).charpoly.IsRoot lam) :
    (complexify A).charpoly.IsRoot lam ∨
      (complexify D).charpoly.IsRoot lam := by
  rw [complexify_fromBlocks] at hroot
  change (Matrix.fromBlocks (complexify A) (fun i j => (B i j : ℂ)) 0
    (complexify D)).charpoly.IsRoot lam at hroot
  erw [Matrix.charpoly_fromBlocks_zero₂₁] at hroot
  exact (mul_eq_zero.mp (by simpa [Polynomial.IsRoot] using hroot))

/-- Strict right-half-plane instability of an upper block-triangular matrix
must occur in one diagonal block. -/
theorem hurwitzUnstable_fromBlocks_zero21_localizes
    {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n]
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ)
    (h : HurwitzUnstable (Matrix.fromBlocks A B 0 D)) :
    HurwitzUnstable A ∨ HurwitzUnstable D := by
  obtain ⟨lam, v, hpos, heig⟩ := h
  have hroot := heig.isRoot_charpoly
  rcases isRoot_fromBlocks_zero21_localizes A B D lam hroot with hA | hD
  · obtain ⟨u, hu⟩ := isRoot_complexified_charpoly_yields_eigenpair A lam hA
    exact Or.inl ⟨lam, u, hpos, hu⟩
  · obtain ⟨u, hu⟩ := isRoot_complexified_charpoly_yields_eigenpair D lam hD
    exact Or.inr ⟨lam, u, hpos, hu⟩

/-- Right column scaling preserves upper block-triangular form and restricts
to the corresponding positive scaling on each diagonal block. -/
theorem rightScale_fromBlocks_zero21
    {m n : Type*}
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ)
    (d : m ⊕ n → ℝ) :
    rightScale (Matrix.fromBlocks A B 0 D) d =
      Matrix.fromBlocks
        (rightScale A (fun i => d (Sum.inl i)))
        (fun i j => B i j * d (Sum.inr j)) 0
        (rightScale D (fun j => d (Sum.inr j))) := by
  ext i j
  cases i <;> cases j <;> simp [rightScale, Matrix.fromBlocks]

/-- D-instability of a block-triangular matrix localizes to a diagonal block;
the off-diagonal coupling cannot manufacture D-instability. -/
theorem dUnstable_fromBlocks_zero21_localizes
    {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n]
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (D : Matrix n n ℝ)
    (h : DUnstable (Matrix.fromBlocks A B 0 D)) :
    DUnstable A ∨ DUnstable D := by
  obtain ⟨d, hd, hscaled⟩ := h
  rw [rightScale_fromBlocks_zero21] at hscaled
  rcases hurwitzUnstable_fromBlocks_zero21_localizes
      (rightScale A (fun i => d (Sum.inl i)))
      (fun i j => B i j * d (Sum.inr j))
      (rightScale D (fun j => d (Sum.inr j))) hscaled with hA | hD
  · exact Or.inl ⟨fun i => d (Sum.inl i), fun i => hd (Sum.inl i), hA⟩
  · exact Or.inr ⟨fun j => d (Sum.inr j), fun j => hd (Sum.inr j), hD⟩

end DUnstableCores

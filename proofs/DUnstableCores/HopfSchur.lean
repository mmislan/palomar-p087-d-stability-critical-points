module

public import proofs.DUnstableCores.RouthHurwitzDim4

@[expose] public section

open scoped ComplexConjugate

namespace DUnstableCores

/-- A matrix with one distinguished articulation coordinate and a branch block. -/
def oneArticulationMatrix {ι : Type*} [Fintype ι]
    (a : ℝ) (r c : ι → ℝ) (B : Matrix ι ι ℝ) :
    Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℝ :=
  fun i j =>
    match i, j with
    | Sum.inl _, Sum.inl _ => a
    | Sum.inl _, Sum.inr j => r j
    | Sum.inr i, Sum.inl _ => c i
    | Sum.inr i, Sum.inr j => B i j

/--
The inverse-free, two-real-coordinate form of a branch solve at frequency `ω`.
The scalar equations are exactly the real and imaginary parts of
`iω - a - r (iωI-B)⁻¹ c = 0`, but no inverse or nonsingularity hypothesis is
needed.
-/
structure HopfBranchSolveWitness {ι : Type*} [Fintype ι]
    (a : ℝ) (r c : ι → ℝ) (B : Matrix ι ι ℝ) (ω : ℝ) where
  u : ι → ℝ
  v : ι → ℝ
  branch_real : ∀ i, -(B.mulVec u i) - ω * v i = c i
  branch_imag : ∀ i, ω * u i - B.mulVec v i = 0
  root_real : a + dotProduct r u = 0
  root_imag : dotProduct r v = ω

/-- Real part of the frequency-dependent Schur message carried by a branch. -/
def HopfBranchSolveWitness.messageReal {ι : Type*} [Fintype ι]
    {a ω : ℝ} {r c : ι → ℝ} {B : Matrix ι ι ℝ}
    (w : HopfBranchSolveWitness a r c B ω) : ℝ :=
  dotProduct r w.u

/-- Imaginary part of the frequency-dependent Schur message carried by a branch. -/
def HopfBranchSolveWitness.messageImag {ι : Type*} [Fintype ι]
    {a ω : ℝ} {r c : ι → ℝ} {B : Matrix ι ι ℝ}
    (w : HopfBranchSolveWitness a r c B ω) : ℝ :=
  dotProduct r w.v

theorem HopfBranchSolveWitness.message_root_equations {ι : Type*} [Fintype ι]
    {a ω : ℝ} {r c : ι → ℝ} {B : Matrix ι ι ℝ}
    (w : HopfBranchSolveWitness a r c B ω) :
    a + w.messageReal = 0 ∧ w.messageImag = ω := by
  exact ⟨w.root_real, w.root_imag⟩

/-- Assemble the real part of the imaginary eigenvector from a branch solve. -/
def HopfBranchSolveWitness.realVector {ι : Type*} [Fintype ι]
    {a ω : ℝ} {r c : ι → ℝ} {B : Matrix ι ι ℝ}
    (w : HopfBranchSolveWitness a r c B ω) : Unit ⊕ ι → ℝ
  | Sum.inl _ => 1
  | Sum.inr i => w.u i

/-- Assemble the imaginary part of the imaginary eigenvector from a branch solve. -/
def HopfBranchSolveWitness.imagVector {ι : Type*} [Fintype ι]
    {a ω : ℝ} {r c : ι → ℝ} {B : Matrix ι ι ℝ}
    (w : HopfBranchSolveWitness a r c B ω) : Unit ⊕ ι → ℝ
  | Sum.inl _ => 0
  | Sum.inr i => w.v i

@[simp] theorem HopfBranchSolveWitness.realVector_inl {ι : Type*} [Fintype ι]
    {a ω : ℝ} {r c : ι → ℝ} {B : Matrix ι ι ℝ}
    (w : HopfBranchSolveWitness a r c B ω) (x : Unit) :
    w.realVector (Sum.inl x) = 1 := by
  rfl

@[simp] theorem HopfBranchSolveWitness.realVector_inr {ι : Type*} [Fintype ι]
    {a ω : ℝ} {r c : ι → ℝ} {B : Matrix ι ι ℝ}
    (w : HopfBranchSolveWitness a r c B ω) (i : ι) :
    w.realVector (Sum.inr i) = w.u i := by
  rfl

@[simp] theorem HopfBranchSolveWitness.imagVector_inl {ι : Type*} [Fintype ι]
    {a ω : ℝ} {r c : ι → ℝ} {B : Matrix ι ι ℝ}
    (w : HopfBranchSolveWitness a r c B ω) (x : Unit) :
    w.imagVector (Sum.inl x) = 0 := by
  rfl

@[simp] theorem HopfBranchSolveWitness.imagVector_inr {ι : Type*} [Fintype ι]
    {a ω : ℝ} {r c : ι → ℝ} {B : Matrix ι ι ℝ}
    (w : HopfBranchSolveWitness a r c B ω) (i : ι) :
    w.imagVector (Sum.inr i) = w.v i := by
  rfl

/--
An exact frequency-dependent branch message satisfying the two root equations
produces an imaginary eigenpair of the full one-articulation matrix.
-/
theorem HopfBranchSolveWitness.hasImaginaryPairWitness {ι : Type*} [Fintype ι]
    {a ω : ℝ} {r c : ι → ℝ} {B : Matrix ι ι ℝ}
    (w : HopfBranchSolveWitness a r c B ω) (hω : 0 < ω) :
    HasImaginaryPairWitness (oneArticulationMatrix a r c B) ω
      w.realVector w.imagVector := by
  refine ⟨hω, Or.inl ?_, ?_⟩
  · intro hzero
    have hroot := congrFun hzero (Sum.inl ())
    simp [HopfBranchSolveWitness.realVector] at hroot
  · intro i
    cases i with
    | inl x =>
        constructor
        · simpa [Matrix.mulVec, oneArticulationMatrix, dotProduct,
            Fintype.sum_sum_type] using w.root_real
        · simpa [Matrix.mulVec, oneArticulationMatrix, dotProduct,
            Fintype.sum_sum_type] using w.root_imag
    | inr i =>
        constructor
        · simp only [Matrix.mulVec, dotProduct, oneArticulationMatrix,
            Fintype.sum_sum_type]
          simp
          have h := w.branch_real i
          simp [Matrix.mulVec, dotProduct] at h
          linarith
        · simp only [Matrix.mulVec, dotProduct, oneArticulationMatrix,
            Fintype.sum_sum_type]
          simp
          have h := w.branch_imag i
          simp [Matrix.mulVec, dotProduct] at h
          linarith

/--
For a singleton branch, the imaginary root equation forces an exact signed
two-cycle identity.  Thus the two directed couplings have opposite signs and
their phase-carrying gain pays the strictly positive cost `b² + ω²`.
-/
theorem HopfBranchSolveWitness.singleton_branch_cycle_identity
    {a ω : ℝ} {r c : Unit → ℝ} {B : Matrix Unit Unit ℝ}
    (w : HopfBranchSolveWitness a r c B ω) (hω : 0 < ω) :
    -(r () * c ()) = (B () ()) ^ 2 + ω ^ 2 := by
  let b : ℝ := B () ()
  let rr : ℝ := r ()
  let cc : ℝ := c ()
  let uu : ℝ := w.u ()
  let vv : ℝ := w.v ()
  have hreal : -b * uu - ω * vv = cc := by
    simpa [b, cc, uu, vv, Matrix.mulVec, dotProduct] using w.branch_real ()
  have himag : ω * uu - b * vv = 0 := by
    simpa [b, uu, vv, Matrix.mulVec, dotProduct] using w.branch_imag ()
  have hroot : rr * vv = ω := by
    simpa [rr, vv, dotProduct] using w.root_imag
  have hv : (b ^ 2 + ω ^ 2) * vv + ω * cc = 0 := by
    linear_combination -b * himag - ω * hreal
  have hfactor : ω * (rr * cc + b ^ 2 + ω ^ 2) = 0 := by
    linear_combination rr * hv - (b ^ 2 + ω ^ 2) * hroot
  have hsum : rr * cc + b ^ 2 + ω ^ 2 = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left hω.ne'
  have hfinal : -(rr * cc) = b ^ 2 + ω ^ 2 := by
    linarith
  simpa [b, rr, cc] using hfinal

theorem HopfBranchSolveWitness.singleton_branch_couplings_opposite
    {a ω : ℝ} {r c : Unit → ℝ} {B : Matrix Unit Unit ℝ}
    (w : HopfBranchSolveWitness a r c B ω) (hω : 0 < ω) :
    r () * c () < 0 := by
  have hid := w.singleton_branch_cycle_identity hω
  have hωsq : 0 < ω ^ 2 := sq_pos_of_pos hω
  nlinarith [sq_nonneg (B () ())]

/-- A normalized singleton branch at a Hopf boundary has zero total diagonal. -/
theorem HopfBranchSolveWitness.singleton_branch_diagonal_balance
    {a ω : ℝ} {r c : Unit → ℝ} {B : Matrix Unit Unit ℝ}
    (w : HopfBranchSolveWitness a r c B ω) (hω : 0 < ω) :
    a + B () () = 0 := by
  let b : ℝ := B () ()
  let rr : ℝ := r ()
  let cc : ℝ := c ()
  let uu : ℝ := w.u ()
  let vv : ℝ := w.v ()
  have hreal : -b * uu - ω * vv = cc := by
    simpa [b, cc, uu, vv, Matrix.mulVec, dotProduct] using w.branch_real ()
  have himag : ω * uu - b * vv = 0 := by
    simpa [b, uu, vv, Matrix.mulVec, dotProduct] using w.branch_imag ()
  have hrootReal : a + rr * uu = 0 := by
    simpa [rr, uu, dotProduct] using w.root_real
  have hcycle : rr * cc + b ^ 2 + ω ^ 2 = 0 := by
    have hid := w.singleton_branch_cycle_identity hω
    dsimp [b, rr, cc]
    linarith
  have hu : (b ^ 2 + ω ^ 2) * uu + b * cc = 0 := by
    linear_combination -b * hreal + ω * himag
  have hfactor : (b ^ 2 + ω ^ 2) * (a + b) = 0 := by
    linear_combination
      (b ^ 2 + ω ^ 2) * hrootReal - rr * hu + b * hcycle
  have hcost : 0 < b ^ 2 + ω ^ 2 := by
    nlinarith [sq_nonneg b, sq_pos_of_pos hω]
  have hab : a + b = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left hcost.ne'
  simpa [b] using hab

/--
The exact two-vertex local-or-circuit dichotomy: either a diagonal is already
positive, or both diagonals vanish and the remaining Hopf mechanism is the
oppositely signed phase-carrying two-cycle.
-/
theorem HopfBranchSolveWitness.singleton_positive_diagonal_or_phase_cycle
    {a ω : ℝ} {r c : Unit → ℝ} {B : Matrix Unit Unit ℝ}
    (w : HopfBranchSolveWitness a r c B ω) (hω : 0 < ω) :
    0 < a ∨ 0 < B () () ∨
      (a = 0 ∧ B () () = 0 ∧ r () * c () < 0) := by
  have hbal := w.singleton_branch_diagonal_balance hω
  have hcycle := w.singleton_branch_couplings_opposite hω
  by_cases ha : 0 < a
  · exact Or.inl ha
  · by_cases hb : 0 < B () ()
    · exact Or.inr (Or.inl hb)
    · right
      right
      have ha0 : a = 0 := by linarith
      have hb0 : B () () = 0 := by linarith
      exact ⟨ha0, hb0, hcycle⟩

end DUnstableCores

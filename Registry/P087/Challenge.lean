module
public import Mathlib

/-! Principal-minor critical-point criteria on Johnson's contact variety. -/
@[expose] public section
noncomputable section
open scoped BigOperators

namespace DUnstableCores
variable {ι : Type*}

/-- Right diagonal scaling: multiply column j by the positive-rate coordinate d j. -/
def rightScale (A : Matrix ι ι ℝ) (d : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => A i j * d j

/-- Embed a real matrix entrywise into the complex numbers. -/
def complexify (A : Matrix ι ι ℝ) : Matrix ι ι ℂ :=
  fun i j => (A i j : ℂ)

/-- A nonzero complex vector satisfying the matrix eigenvalue equation. -/
def HasEigenpair [Fintype ι] (A : Matrix ι ι ℝ) (lam : ℂ) (v : ι → ℂ) : Prop :=
  v ≠ 0 ∧ ∀ i, Matrix.mulVec (complexify A) v i = lam * v i

/-- Existence of an eigenvalue with strictly positive real part. -/
def HurwitzUnstable [Fintype ι] (A : Matrix ι ι ℝ) : Prop :=
  ∃ lam : ℂ, ∃ v : ι → ℂ, 0 < lam.re ∧ HasEigenpair A lam v

/-- Absence of strictly positive-real-part eigenvalues; imaginary-axis roots are allowed. -/
def HurwitzNonpositive [Fintype ι] (A : Matrix ι ι ℝ) : Prop :=
  ¬ HurwitzUnstable A

/-- Every complex eigenvalue has strictly negative real part. -/
def HurwitzStable [Fintype ι] (A : Matrix ι ι ℝ) : Prop :=
  ∀ lam : ℂ, ∀ v : ι → ℂ, HasEigenpair A lam v → lam.re < 0

/-- Some strictly positive right diagonal scaling is strictly Hurwitz-unstable. -/
def DUnstable [Fintype ι] (A : Matrix ι ι ℝ) : Prop :=
  ∃ d : ι → ℝ, (∀ i, 0 < d i) ∧ HurwitzUnstable (rightScale A d)

/-- Every strictly positive right diagonal scaling is Hurwitz-stable. -/
def DStable [Fintype ι] (A : Matrix ι ι ℝ) : Prop :=
  ∀ d : ι → ℝ, (∀ i, 0 < d i) → HurwitzStable (rightScale A d)

/-- Every strictly positive right diagonal scaling has no strict growth. -/
def DNonUnstable [Fintype ι] (A : Matrix ι ι ℝ) : Prop :=
  ∀ d : ι → ℝ, (∀ i, 0 < d i) → HurwitzNonpositive (rightScale A d)

end DUnstableCores

namespace DStability5x5
open DUnstableCores Matrix Finset
variable {n : ℕ}

/-- Complex transposed minor matrix: columns of -A on S and identity columns outside S. -/
def pminorMat (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) : Matrix (Fin n) (Fin n) ℂ :=
  fun l k => if l ∈ S then ((-A k l : ℝ) : ℂ) else (if l = k then 1 else 0)

/-- Determinant of the transposed principal-minor matrix, embedded in the complex numbers. -/
def pminor (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) : ℂ := (pminorMat A S).det

/-- Explicit principal-minor polynomial for det(i*I - A*diag(d)). -/
def contactPoly (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) : ℂ :=
  ∑ S : Finset (Fin n), Complex.I ^ (n - S.card) * (∏ l ∈ S, (d l : ℂ)) * pminor A S

/-- Explicit coordinate partial derivative of the contact polynomial. -/
def partialPoly (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) (i : Fin n) : ℂ :=
  ∑ S : Finset (Fin n), if i ∈ S then
    Complex.I ^ (n - S.card) * (∏ l ∈ S.erase i, (d l : ℂ)) * pminor A S else 0

/-- Real determinant of the principal submatrix of -A indexed by S. -/
def minorR (A : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Fin n)) : ℝ :=
  ((-A).submatrix (fun i : S => (i : Fin n)) (fun i : S => (i : Fin n))).det

/-- Sum of size-k principal minors of -A weighted by products of the corresponding rates. -/
def ck (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (d : Fin n → ℝ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card = k),
    minorR A S * ∏ l ∈ S, d l

/-- Coordinate derivative of ck, expressed by minors containing the selected coordinate. -/
def ckPart (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (d : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card = k ∧ i ∈ S),
    minorR A S * ∏ l ∈ S.erase i, d l

/-- For every dimension, D-stability is equivalent to Hurwitz stability and absence of positive contact points satisfying the explicit principal-minor Fritz-John system. The selected 5x5 specialization states both the Lagrange and tangency branches with explicit coefficient sums and positive barrier weights. -/
theorem dStable_iff_explicit (a b : Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    DStable A ↔ HurwitzStable A ∧ ¬ ∃ d : Fin n → ℝ, (∀ i, 0 < d i) ∧ contactPoly A d = 0 ∧
      ∃ Λ : Fin 2 → ℝ, ∃ Λ₀ : ℝ, (Λ, Λ₀) ≠ 0 ∧ ∀ i : Fin n,
        Λ 0 * (partialPoly A d i).re + Λ 1 * (partialPoly A d i).im +
          Λ₀ * (a i - b i / d i) = 0 := by
  sorry

theorem dStable_iff_five (a b : Fin 5 → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (A : Matrix (Fin 5) (Fin 5) ℝ) :
    DStable A ↔ HurwitzStable A ∧
      (¬ ∃ (d : Fin 5 → ℝ) (lam mu : ℝ), (∀ i, 0 < d i) ∧
          ck A 1 d - ck A 3 d + ck A 5 d = 0 ∧ 1 - ck A 2 d + ck A 4 d = 0 ∧
          ∀ i, a i * d i - b i =
            lam * (d i * (ckPart A 1 d i - ckPart A 3 d i + ckPart A 5 d i)) +
              mu * (d i * (ckPart A 4 d i - ckPart A 2 d i))) ∧
      (¬ ∃ (d : Fin 5 → ℝ) (t : ℝ), (∀ i, 0 < d i) ∧
          ck A 1 d - ck A 3 d + ck A 5 d = 0 ∧ 1 - ck A 2 d + ck A 4 d = 0 ∧
          ∀ i, (1 - t ^ 2) * (ckPart A 1 d i - ckPart A 3 d i + ckPart A 5 d i) +
            2 * t * (ckPart A 4 d i - ckPart A 2 d i) = 0) := by
  sorry

end DStability5x5

end

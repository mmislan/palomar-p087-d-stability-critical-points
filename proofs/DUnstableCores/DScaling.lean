module

public import Mathlib

@[expose] public section

/-!
# Right diagonal scaling and spectral semantics

The D-unstable-core conjecture uses right scaling `A * Diag(d)`.  This module
defines that operation entrywise, avoiding any accidental identification with
additive degradation or left scaling.
-/

namespace DUnstableCores

open scoped ComplexConjugate

variable {ι : Type*}

/-- Right multiplication by a diagonal vector: column `j` is scaled by `d j`. -/
def rightScale (A : Matrix ι ι ℝ) (d : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => A i j * d j

@[simp] theorem rightScale_apply (A : Matrix ι ι ℝ) (d : ι → ℝ) (i j : ι) :
    rightScale A d i j = A i j * d j := rfl

@[simp] theorem rightScale_one (A : Matrix ι ι ℝ) :
    rightScale A (fun _ => 1) = A := by
  ext i j
  simp [rightScale]

/-- Entrywise embedding of a real matrix into the complex numbers. -/
def complexify (A : Matrix ι ι ℝ) : Matrix ι ι ℂ :=
  fun i j => (A i j : ℂ)

/-- An eigenpair predicate stated directly through matrix-vector multiplication. -/
def HasEigenpair [Fintype ι] (A : Matrix ι ι ℝ) (lam : ℂ) (v : ι → ℂ) : Prop :=
  v ≠ 0 ∧ ∀ i, Matrix.mulVec (complexify A) v i = lam * v i

/-- Strict open-right-half-plane instability.  Imaginary-axis roots are not
classified as unstable by this predicate. -/
def HurwitzUnstable [Fintype ι] (A : Matrix ι ι ℝ) : Prop :=
  ∃ lam : ℂ, ∃ v : ι → ℂ, 0 < lam.re ∧ HasEigenpair A lam v

def HurwitzNonpositive [Fintype ι] (A : Matrix ι ι ℝ) : Prop :=
  ¬ HurwitzUnstable A

/-- Strict Hurwitz stability.  This excludes imaginary-axis eigenvalues. -/
def HurwitzStable [Fintype ι] (A : Matrix ι ι ℝ) : Prop :=
  ∀ lam : ℂ, ∀ v : ι → ℂ, HasEigenpair A lam v → lam.re < 0

/-- Existential instability under a strictly positive right diagonal scaling. -/
def DUnstable [Fintype ι] (A : Matrix ι ι ℝ) : Prop :=
  ∃ d : ι → ℝ, (∀ i, 0 < d i) ∧ HurwitzUnstable (rightScale A d)

/-- Universal stability under every strictly positive right diagonal scaling. -/
def DStable [Fintype ι] (A : Matrix ι ι ℝ) : Prop :=
  ∀ d : ι → ℝ, (∀ i, 0 < d i) → HurwitzStable (rightScale A d)

/-- The exact universal negation required by a counterexample to D-core
necessity.  Unlike `DStable`, this permits imaginary-axis boundary roots. -/
def DNonUnstable [Fintype ι] (A : Matrix ι ι ℝ) : Prop :=
  ∀ d : ι → ℝ, (∀ i, 0 < d i) → HurwitzNonpositive (rightScale A d)

theorem not_dNonUnstable_iff_dUnstable [Fintype ι] (A : Matrix ι ι ℝ) :
    ¬ DNonUnstable A ↔ DUnstable A := by
  constructor
  · intro hnotNonUnstable
    by_contra hnotUnstable
    apply hnotNonUnstable
    intro d hd hscaled
    exact hnotUnstable ⟨d, hd, hscaled⟩
  · rintro ⟨d, hd, hscaled⟩ hnon
    exact (hnon d hd) hscaled

theorem dStable_implies_dNonUnstable [Fintype ι] (A : Matrix ι ι ℝ)
    (hstable : DStable A) : DNonUnstable A := by
  intro d hd hunstable
  rcases hunstable with ⟨lam, v, hpos, heig⟩
  have hneg := hstable d hd lam v heig
  linarith

theorem hurwitzUnstable_implies_dUnstable [Fintype ι]
    (A : Matrix ι ι ℝ) (h : HurwitzUnstable A) : DUnstable A := by
  refine ⟨fun _ => 1, by simp, ?_⟩
  simpa using h

/-- Exact real positive eigenpair witness, used by the positive-real branch. -/
def HasPositiveRealEigenpair [Fintype ι] (A : Matrix ι ι ℝ) : Prop :=
  ∃ lam : ℝ, ∃ v : ι → ℝ, 0 < lam ∧ v ≠ 0 ∧
    ∀ i, Matrix.mulVec A v i = lam * v i

end DUnstableCores

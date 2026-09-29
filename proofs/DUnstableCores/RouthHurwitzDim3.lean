module

public import proofs.DUnstableCores.ComplexReduction

@[expose] public section

/-!
# Exact cubic Routh--Hurwitz boundary theorem

For a monic cubic `X^3 + a₁ X^2 + a₂ X + a₃`, coefficientwise
nonnegativity together with `a₁*a₂-a₃ ≥ 0` excludes every eigenvalue in the
open right half-plane.  Weak inequalities are intentional: imaginary-axis
and zero roots belong to `HurwitzNonpositive`, not strict Hurwitz stability.
-/

namespace DUnstableCores

open Polynomial

/-- Exact cubic characteristic-polynomial presentation. -/
def IsCubicCharpoly
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (a₁ a₂ a₃ : ℝ) : Prop :=
  A.charpoly = X ^ 3 + C a₁ * X ^ 2 + C a₂ * X + C a₃

/-- The weak cubic Routh--Hurwitz conditions are sound for the campaign's
open-right-half-plane non-instability semantics, including degenerate
boundary branches. -/
theorem hurwitzNonpositive_of_cubic_coeff_nonneg_delta_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (a₁ a₂ a₃ : ℝ)
    (hpoly : IsCubicCharpoly A a₁ a₂ a₃)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃)
    (hdelta : 0 ≤ a₁ * a₂ - a₃) :
    HurwitzNonpositive A := by
  intro hunstable
  obtain ⟨lam, v, hlam, heig⟩ := hunstable
  have hroot := heig.isRoot_charpoly
  have hmap : (complexify A).charpoly =
      A.charpoly.map (algebraMap ℝ ℂ) := by
    have hmatrix : complexify A = A.map (algebraMap ℝ ℂ) := by
      ext i j
      rfl
    rw [hmatrix]
    exact Matrix.charpoly_map A (algebraMap ℝ ℂ)
  rw [hmap, hpoly] at hroot
  have hp := hroot.eq_zero
  have hre := congrArg Complex.re hp
  have him := congrArg Complex.im hp
  simp [pow_succ, Complex.mul_re, Complex.mul_im] at hre him
  by_cases himzero : lam.im = 0
  · have hx3 : 0 < lam.re ^ 3 := pow_pos hlam 3
    rw [himzero] at hre
    norm_num at hre
    nlinarith [mul_nonneg ha₁ (sq_nonneg lam.re), mul_nonneg ha₂ hlam.le]
  · have hfactor :
        lam.im * (3 * lam.re ^ 2 - lam.im ^ 2 + 2 * a₁ * lam.re + a₂) = 0 := by
      nlinarith [him]
    have hbracket :
        3 * lam.re ^ 2 - lam.im ^ 2 + 2 * a₁ * lam.re + a₂ = 0 :=
      (mul_eq_zero.mp hfactor).resolve_left himzero
    have hx3 : 0 < lam.re ^ 3 := pow_pos hlam 3
    have hmain :
        8 * lam.re ^ 3 + 8 * a₁ * lam.re ^ 2 +
          2 * (a₁ ^ 2 + a₂) * lam.re + (a₁ * a₂ - a₃) = 0 := by
      nlinarith [hre, hbracket]
    have hterm1 : 0 < 8 * lam.re ^ 3 := mul_pos (by norm_num) hx3
    have hterm2 : 0 ≤ 8 * a₁ * lam.re ^ 2 := by positivity
    have hterm3 : 0 ≤ 2 * (a₁ ^ 2 + a₂) * lam.re := by positivity
    nlinarith

/-- With nonnegative cubic coefficients, a strict right-half-plane
instability forces strict failure of the second Routh--Hurwitz determinant. -/
theorem cubic_hurwitzUnstable_implies_delta_negative
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (a₁ a₂ a₃ : ℝ)
    (hpoly : IsCubicCharpoly A a₁ a₂ a₃)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃)
    (hunstable : HurwitzUnstable A) :
    a₁ * a₂ - a₃ < 0 := by
  by_contra hnot
  have hdelta : 0 ≤ a₁ * a₂ - a₃ := le_of_not_gt hnot
  exact (hurwitzNonpositive_of_cubic_coeff_nonneg_delta_nonneg
    A a₁ a₂ a₃ hpoly ha₁ ha₂ ha₃ hdelta) hunstable

/-- A complex root of the complexified characteristic polynomial supplies a
direct matrix eigenpair witness. -/
theorem hasEigenpair_of_isRoot_complexified_charpoly
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} {lam : ℂ}
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

/-- Strict failure of the cubic determinant, with nonnegative coefficients,
is sufficient for open-right-half-plane instability. -/
theorem cubic_delta_negative_implies_hurwitzUnstable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (a₁ a₂ a₃ : ℝ)
    (hpoly : IsCubicCharpoly A a₁ a₂ a₃)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃)
    (hdelta : a₁ * a₂ - a₃ < 0) :
    HurwitzUnstable A := by
  classical
  let p : ℝ[X] := X ^ 3 + C a₁ * X ^ 2 + C a₂ * X + C a₃
  have hpdeg : p.natDegree = 3 := by
    dsimp [p]
    rw [show (X : ℝ[X]) ^ 3 = C 1 * X ^ 3 by simp]
    exact natDegree_cubic one_ne_zero
  have hplead : 0 ≤ p.leadingCoeff := by
    dsimp [p]
    rw [show (X : ℝ[X]) ^ 3 = C 1 * X ^ 3 by simp,
      leadingCoeff_cubic one_ne_zero]
    norm_num
  have hpeval : 0 < p.eval (-a₁) := by
    simp [p]
    nlinarith
  have hexists : ∃ r : ℝ, p.IsRoot r ∧ r ≤ -a₁ := by
    by_contra hnone
    push Not at hnone
    have hsign := zero_lt_negOnePow_mul_eval_of_lt_roots_of_leadingCoeff_nonneg
      (P := p) (x := -a₁) hnone hplead
    rw [hpdeg] at hsign
    norm_num at hsign
    nlinarith
  obtain ⟨r, hr, hrle⟩ := hexists
  have hrlt : r < -a₁ := by
    refine lt_of_le_of_ne hrle ?_
    intro hre
    have : p.eval (-a₁) = 0 := by
      rw [← hre]
      exact hr.eq_zero
    linarith
  have hrneg : r < 0 := lt_of_lt_of_le hrlt (neg_nonpos.mpr ha₁)
  have ha₃ne : a₃ ≠ 0 := by
    intro ha₃zero
    rw [ha₃zero] at hdelta
    nlinarith [mul_nonneg ha₁ ha₂]
  have ha₃pos : 0 < a₃ := lt_of_le_of_ne ha₃ (Ne.symm ha₃ne)
  have hrealeq : r ^ 3 + a₁ * r ^ 2 + a₂ * r + a₃ = 0 := by
    have := hr.eq_zero
    simpa [p] using this
  let b : ℝ := a₁ + r
  let c : ℝ := a₂ + a₁ * r + r ^ 2
  have hbneg : b < 0 := by dsimp [b]; linarith
  have hrc : -r * c = a₃ := by
    dsimp [c]
    nlinarith [hrealeq]
  have hcpos : 0 < c := by
    by_contra hc
    have hcnonpos : c ≤ 0 := le_of_not_gt hc
    have : -r * c ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt (neg_pos.mpr hrneg)) hcnonpos
    nlinarith
  let q : ℂ[X] := X ^ 2 + C (b : ℂ) * X + C (c : ℂ)
  have hqdeg : q.degree ≠ 0 := by
    have hdegree : q.degree = 2 := by
      dsimp [q]
      rw [show (X : ℂ[X]) ^ 2 = C 1 * X ^ 2 by simp]
      exact degree_quadratic one_ne_zero
    rw [hdegree]
    norm_num
  obtain ⟨lam, hlamroot⟩ := IsAlgClosed.exists_root q hqdeg
  have hqeq : lam ^ 2 + (b : ℂ) * lam + (c : ℂ) = 0 := by
    simpa [q] using hlamroot.eq_zero
  have hlamre : 0 < lam.re := by
    have hre := congrArg Complex.re hqeq
    have him := congrArg Complex.im hqeq
    simp [pow_two, Complex.mul_re, Complex.mul_im] at hre him
    by_cases himzero : lam.im = 0
    · rw [himzero] at hre
      norm_num at hre
      by_contra hnot
      have hx : lam.re ≤ 0 := le_of_not_gt hnot
      nlinarith [sq_nonneg lam.re]
    · have hfactor : lam.im * (2 * lam.re + b) = 0 := by
        nlinarith [him]
      have : 2 * lam.re + b = 0 :=
        (mul_eq_zero.mp hfactor).resolve_left himzero
      nlinarith
  have hpcomplex :
      lam ^ 3 + (a₁ : ℂ) * lam ^ 2 + (a₂ : ℂ) * lam + (a₃ : ℂ) = 0 := by
    have hconstant : (-r : ℂ) * (c : ℂ) = (a₃ : ℂ) := by
      exact_mod_cast hrc
    calc
      lam ^ 3 + (a₁ : ℂ) * lam ^ 2 + (a₂ : ℂ) * lam + (a₃ : ℂ) =
          (lam - (r : ℂ)) * (lam ^ 2 + (b : ℂ) * lam + (c : ℂ)) := by
            rw [← hconstant]
            simp only [b, c, Complex.ofReal_add, Complex.ofReal_mul,
              Complex.ofReal_pow]
            ring
      _ = 0 := by rw [hqeq, mul_zero]
  have hrootA : (complexify A).charpoly.IsRoot lam := by
    have hmap : (complexify A).charpoly =
        A.charpoly.map (algebraMap ℝ ℂ) := by
      have hmatrix : complexify A = A.map (algebraMap ℝ ℂ) := by
        ext i j
        rfl
      rw [hmatrix]
      exact Matrix.charpoly_map A (algebraMap ℝ ℂ)
    rw [hmap, hpoly]
    simpa using hpcomplex
  obtain ⟨v, heig⟩ := hasEigenpair_of_isRoot_complexified_charpoly hrootA
  exact ⟨lam, v, hlamre, heig⟩

/-- Data-bearing weak cubic Routh--Hurwitz certificate. -/
structure RouthHurwitz3NonpositiveCertificate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) where
  a₁ : ℝ
  a₂ : ℝ
  a₃ : ℝ
  charpoly_eq : IsCubicCharpoly A a₁ a₂ a₃
  a₁_nonneg : 0 ≤ a₁
  a₂_nonneg : 0 ≤ a₂
  a₃_nonneg : 0 ≤ a₃
  delta₂_nonneg : 0 ≤ a₁ * a₂ - a₃

theorem RouthHurwitz3NonpositiveCertificate.sound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (c : RouthHurwitz3NonpositiveCertificate A) :
    HurwitzNonpositive A :=
  hurwitzNonpositive_of_cubic_coeff_nonneg_delta_nonneg
    A c.a₁ c.a₂ c.a₃ c.charpoly_eq c.a₁_nonneg c.a₂_nonneg
      c.a₃_nonneg c.delta₂_nonneg

/-- Every `Fin 3` characteristic polynomial is the literal monic cubic whose
three lower coefficients are read from `Matrix.charpoly`. -/
theorem isCubicCharpoly_fin_three (A : Matrix (Fin 3) (Fin 3) ℝ) :
    IsCubicCharpoly A (A.charpoly.coeff 2) (A.charpoly.coeff 1)
      (A.charpoly.coeff 0) := by
  unfold IsCubicCharpoly
  have hnat : A.charpoly.natDegree = 3 := by
    simp
  have hcoeff3 : A.charpoly.coeff 3 = 1 := by
    have h := A.charpoly_monic.coeff_natDegree
    simp only [hnat] at h
    exact h
  ext n
  by_cases hn : n ≤ 3
  · interval_cases n <;> simp [hcoeff3]
  · have hzero : A.charpoly.coeff n = 0 :=
      coeff_eq_zero_of_natDegree_lt (by omega)
    have hrightDegree :
        (X ^ 3 + C (A.charpoly.coeff 2) * X ^ 2 +
          C (A.charpoly.coeff 1) * X +
          C (A.charpoly.coeff 0)).natDegree = 3 := by
      rw [show (X : ℝ[X]) ^ 3 = C 1 * X ^ 3 by simp]
      exact natDegree_cubic one_ne_zero
    have hright :
        (X ^ 3 + C (A.charpoly.coeff 2) * X ^ 2 +
          C (A.charpoly.coeff 1) * X +
          C (A.charpoly.coeff 0)).coeff n = 0 :=
      coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hzero, hright]

/-- Exact source-level reduction at dimension three: under the no-D-unstable
child hypothesis, any remaining instability forces negative `Delta_2` of the
literal source characteristic polynomial. -/
theorem fin_three_noDUnstableChild_instability_forces_delta₂_negative
    {Reaction : Type*} [Fintype Reaction] [DecidableEq Reaction]
    (Q : SourceNetwork (Fin 3) Reaction) (R : Reactivity Q)
    (hchildren : ∀ child : ChildSelection Q,
      DNonUnstable child.realMatrix)
    (hunstable : HurwitzUnstable (Q.jacobian R)) :
    (Q.jacobian R).charpoly.coeff 2 *
        (Q.jacobian R).charpoly.coeff 1 -
      (Q.jacobian R).charpoly.coeff 0 < 0 := by
  have hcoeff := dNonUnstable_children_imply_charpoly_coeff_nonneg Q R hchildren
  exact cubic_hurwitzUnstable_implies_delta_negative
    (Q.jacobian R)
    ((Q.jacobian R).charpoly.coeff 2)
    ((Q.jacobian R).charpoly.coeff 1)
    ((Q.jacobian R).charpoly.coeff 0)
    (isCubicCharpoly_fin_three (Q.jacobian R))
    (hcoeff 2) (hcoeff 1) (hcoeff 0) hunstable

end DUnstableCores

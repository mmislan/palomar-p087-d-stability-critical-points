module

public import proofs.DStability5x5.ProperExhaustion
public import proofs.DStability5x5.ContactExpansion

@[expose] public section

/-!
# Theorem 5 in explicit polynomial coordinates (all n; n = 5 is the target case)

With `contactPoly A d = ∑ S, i^(n-|S|) (∏_{l∈S} d_l) pminor A S` (= `contactDet A d`, by
`contactDet_expansion`) and its explicit partial derivatives

  `partialPoly A d i = ∑_{S ∋ i} i^(n-|S|) (∏_{l∈S∖{i}} d_l) pminor A S`,

Theorem M for the weighted log barrier `ψ = ∑ a_i d_i - b_i log d_i` reads:

  `A` is D-stable  ⇔  `A` is Hurwitz and there is no `d > 0` with `contactPoly A d = 0` and a
  nonzero `(Λ₁, Λ₂, Λ₀)` such that for every `i`
  `Λ₁ Re ∂_i + Λ₂ Im ∂_i + Λ₀ (a_i - b_i / d_i) = 0`.

The case `Λ₀ ≠ 0` is the Lagrange system (b) of THEOREM_5x5.md (multiply the i-th equation by
`d_i`); the case `Λ₀ = 0` is the tangency system (c).
-/

noncomputable section

open Matrix Finset

namespace DStability5x5

open DUnstableCores

variable {n : ℕ}

/-- The contact polynomial in explicit principal-minor form. -/
def contactPoly (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) : ℂ :=
  ∑ S : Finset (Fin n), Complex.I ^ (n - S.card) * (∏ l ∈ S, (d l : ℂ)) * pminor A S

/-- Explicit partial derivative of the contact polynomial in direction `d_i`. -/
def partialPoly (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) (i : Fin n) : ℂ :=
  ∑ S : Finset (Fin n), if i ∈ S then
    Complex.I ^ (n - S.card) * (∏ l ∈ S.erase i, (d l : ℂ)) * pminor A S else 0

theorem contactDet_eq_poly (A : Matrix (Fin n) (Fin n) ℝ) :
    contactDet A = contactPoly A := by
  funext d
  exact contactDet_expansion A d

/-- The coordinate projection composed with the real-to-complex embedding. -/
def cproj (l : Fin n) : (Fin n → ℝ) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (ContinuousLinearMap.proj l)

theorem monomial_hasFDerivAt (S : Finset (Fin n)) (d : Fin n → ℝ) :
    HasFDerivAt (fun x : Fin n → ℝ => ∏ l ∈ S, (x l : ℂ))
      (∑ l ∈ S, (∏ j ∈ S.erase l, (d j : ℂ)) • cproj l) d := by
  classical
  have h : ∀ l ∈ S, HasFDerivAt (fun x : Fin n → ℝ => (x l : ℂ)) (cproj l) d := by
    intro l _
    exact (cproj l).hasFDerivAt
  exact HasFDerivAt.finsetProd h

/-- The explicit derivative of the contact polynomial. -/
def contactDeriv (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℂ :=
  ∑ S : Finset (Fin n), (Complex.I ^ (n - S.card) * pminor A S) •
    ∑ l ∈ S, (∏ j ∈ S.erase l, (d j : ℂ)) • cproj l

theorem contactPoly_hasFDerivAt (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) :
    HasFDerivAt (contactPoly A) (contactDeriv A d) d := by
  classical
  unfold contactPoly contactDeriv
  apply HasFDerivAt.fun_sum
  intro S _
  have hm := monomial_hasFDerivAt S d
  have h2 := hm.const_smul (Complex.I ^ (n - S.card) * pminor A S)
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards with x
  show (Complex.I ^ (n - S.card) * ∏ l ∈ S, (x l : ℂ)) * pminor A S =
    (Complex.I ^ (n - S.card) * pminor A S) • ∏ l ∈ S, (x l : ℂ)
  rw [smul_eq_mul]
  ring

theorem contactDeriv_single (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) (i : Fin n) :
    contactDeriv A d (Pi.single i 1) = partialPoly A d i := by
  classical
  unfold contactDeriv partialPoly
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hinner : ∑ l ∈ S, (∏ j ∈ S.erase l, (d j : ℂ)) * cproj l (Pi.single i 1) =
      if i ∈ S then ∏ j ∈ S.erase i, (d j : ℂ) else 0 := by
    have hc : ∀ l, cproj l (Pi.single i (1 : ℝ)) = if l = i then (1 : ℂ) else 0 := by
      intro l
      simp only [cproj, ContinuousLinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearMap.proj_apply, Complex.ofRealCLM_apply]
      by_cases h : l = i
      · subst h; simp
      · simp [h]
    simp only [hc, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
  rw [hinner]
  split_ifs <;> ring

theorem contactRe_fderiv_single (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) (i : Fin n) :
    fderiv ℝ (contactRe A) d (Pi.single i 1) = (partialPoly A d i).re := by
  have h : HasFDerivAt (contactRe A) (Complex.reCLM.comp (contactDeriv A d)) d := by
    have hc := contactPoly_hasFDerivAt A d
    rw [← contactDet_eq_poly] at hc
    exact Complex.reCLM.hasFDerivAt.comp d hc
  rw [h.fderiv]
  simp [contactDeriv_single]

theorem contactIm_fderiv_single (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) (i : Fin n) :
    fderiv ℝ (contactIm A) d (Pi.single i 1) = (partialPoly A d i).im := by
  have h : HasFDerivAt (contactIm A) (Complex.imCLM.comp (contactDeriv A d)) d := by
    have hc := contactPoly_hasFDerivAt A d
    rw [← contactDet_eq_poly] at hc
    exact Complex.imCLM.hasFDerivAt.comp d hc
  rw [h.fderiv]
  simp [contactDeriv_single]

theorem psiL_fderiv_single (a b : Fin n → ℝ) {d : Fin n → ℝ} (hd : ∀ i, 0 < d i) (i : Fin n) :
    fderiv ℝ (psiL a b) d (Pi.single i 1) = a i - b i / d i := by
  classical
  let P : Fin n → (Fin n → ℝ) →L[ℝ] ℝ := fun j =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j
  have hterm : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      HasFDerivAt (fun x : Fin n → ℝ => a j * x j - b j * Real.log (x j))
        (a j • P j - (b j * (d j)⁻¹) • P j) d := by
    intro j _
    have hp : HasFDerivAt (fun x : Fin n → ℝ => x j) (P j) d := (P j).hasFDerivAt
    have hl : HasFDerivAt (fun x : Fin n → ℝ => Real.log (x j)) ((d j)⁻¹ • P j) d := by
      have := (Real.hasDerivAt_log (ne_of_gt (hd j))).comp_hasFDerivAt d hp
      simpa only [Function.comp_def] using! this
    have h1 := hp.const_mul (a j)
    have h2 := hl.const_mul (b j)
    have h3 := h1.sub h2
    convert h3 using 1
    ext v
    simp [smul_eq_mul, P]
    ring
  have hsum := HasFDerivAt.fun_sum hterm
  have hpsi : psiL a b = fun x => ∑ j ∈ (Finset.univ : Finset (Fin n)), (a j * x j - b j * Real.log (x j)) := by
    funext x
    rfl
  rw [hpsi, hsum.fderiv]
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_sub,
    FunLike.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, P,
    ContinuousLinearMap.proj_apply]
  rw [Finset.sum_eq_single i]
  · simp [div_eq_mul_inv]
  · intro j _ hj
    simp [hj]
  · simp

/-- A continuous linear functional on `Fin n → ℝ` vanishes iff it vanishes on the unit vectors. -/
theorem clm_eq_zero_iff_single (L : (Fin n → ℝ) →L[ℝ] ℝ) :
    L = 0 ↔ ∀ i, L (Pi.single i 1) = 0 := by
  classical
  constructor
  · intro h i
    simp [h]
  · intro h
    ext v
    have hv : v = ∑ i, v i • Pi.single i (1 : ℝ) := by
      funext k
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hv, map_sum]
    simp [h]

/-- **Theorem 5 in explicit coordinates** (log barrier, weights `a, b > 0`). -/
theorem dStable_iff_explicit (a b : Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    DStable A ↔ HurwitzStable A ∧ ¬ ∃ d : Fin n → ℝ, (∀ i, 0 < d i) ∧ contactPoly A d = 0 ∧
      ∃ Λ : Fin 2 → ℝ, ∃ Λ₀ : ℝ, (Λ, Λ₀) ≠ 0 ∧ ∀ i : Fin n,
        Λ 0 * (partialPoly A d i).re + Λ 1 * (partialPoly A d i).im +
          Λ₀ * (a i - b i / d i) = 0 := by
  rw [dStable_iff_morse_logBarrier a b ha hb A]
  apply and_congr_right
  intro _
  apply not_congr
  apply exists_congr
  intro d
  constructor
  · rintro ⟨hd, hc, Λ, Λ₀, hne, hsum⟩
    refine ⟨hd, by rw [← contactDet_eq_poly]; exact hc, Λ, Λ₀, hne, fun i => ?_⟩
    have := congrArg (fun L => L (Pi.single i 1)) hsum
    simp only [_root_.add_apply, FunLike.coe_smul, Pi.smul_apply,
      smul_eq_mul, _root_.zero_apply] at this
    rw [contactRe_fderiv_single, contactIm_fderiv_single] at this
    have hψ : fderiv ℝ (psiLExhaustion a b ha hb).f d (Pi.single i 1) = a i - b i / d i :=
      psiL_fderiv_single a b hd i
    rw [hψ] at this
    exact this
  · rintro ⟨hd, hc, Λ, Λ₀, hne, heq⟩
    refine ⟨hd, by rw [contactDet_eq_poly]; exact hc, Λ, Λ₀, hne, ?_⟩
    rw [clm_eq_zero_iff_single]
    intro i
    simp only [_root_.add_apply, FunLike.coe_smul, Pi.smul_apply,
      smul_eq_mul]
    rw [contactRe_fderiv_single, contactIm_fderiv_single]
    have hψ : fderiv ℝ (psiLExhaustion a b ha hb).f d (Pi.single i 1) = a i - b i / d i :=
      psiL_fderiv_single a b hd i
    rw [hψ]
    exact heq i

end DStability5x5

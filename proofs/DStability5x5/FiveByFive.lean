module

public import proofs.DStability5x5.ExplicitCriterion
public import proofs.DStability5x5.PrincipalMinor

@[expose] public section

/-!
# The Lagrange / tangency split of Theorem 5, and the explicit 5×5 criterion

`dStable_iff_explicit` asks for a nonzero multiplier `(Λ₁, Λ₂, Λ₀)` with
`Λ₁ Re ∂_i + Λ₂ Im ∂_i + Λ₀ (a_i - b_i / d_i) = 0` on the contact variety.  Splitting on `Λ₀`:

* `Λ₀ ≠ 0` gives the **Lagrange system** (b): `a_i d_i - b_i = λ d_i Re ∂_i + μ d_i Im ∂_i`;
* `Λ₀ = 0` gives the **tangency system** (c): `(1 - t²) Re ∂_i + 2 t Im ∂_i = 0` for one `t`
  (the direction `[Λ₁ : Λ₂]` is parametrised rationally by `(1 - t², 2t)`).

For `n = 5` the real and imaginary parts of the contact polynomial and of its partial
derivatives are written with the weighted principal-minor sums
`c_k(d) = ∑_{|S| = k} m_S ∏_{l ∈ S} d_l` and `c_k^{(i)}(d) = ∑_{|S| = k, i ∈ S} m_S ∏_{l ∈ S∖i} d_l`,
`m_S = det ((-A)[S])`:

  `Re P = c₁ - c₃ + c₅`,  `Im P = 1 - c₂ + c₄`,
  `Re ∂_i P = c₁⁽ⁱ⁾ - c₃⁽ⁱ⁾ + c₅⁽ⁱ⁾`,  `Im ∂_i P = -c₂⁽ⁱ⁾ + c₄⁽ⁱ⁾`.
-/

noncomputable section

open Matrix Finset

namespace DStability5x5

open DUnstableCores

variable {n : ℕ}

/-! ### Real-algebra helpers for the split -/

theorem lagrange_fwd (p q c x y α β δ : ℝ) (hc : c ≠ 0) (hδ : δ ≠ 0)
    (h : p * x + q * y + c * (α - β / δ) = 0) :
    α * δ - β = (-p / c) * (δ * x) + (-q / c) * (δ * y) := by
  have hb : β / δ * δ = β := div_mul_cancel₀ β hδ
  have key : c * (α * δ - β) = -(p * (δ * x)) - q * (δ * y) := by
    linear_combination δ * h + c * hb
  have hinv : c⁻¹ * c = 1 := inv_mul_cancel₀ hc
  linear_combination c⁻¹ * key - (α * δ - β) * hinv

theorem lagrange_bwd (lam mu x y α β δ : ℝ) (hδ : δ ≠ 0)
    (h : α * δ - β = lam * (δ * x) + mu * (δ * y)) :
    -lam * x + -mu * y + 1 * (α - β / δ) = 0 := by
  have hinv : δ * δ⁻¹ = 1 := mul_inv_cancel₀ hδ
  linear_combination δ⁻¹ * h - (α - lam * x - mu * y) * hinv

/-- Rational parameter of the projective direction `[p : q]` along the curve `(1 - t², 2t)`. -/
def tpar (p q : ℝ) : ℝ := if q = 0 then 0 else (Real.sqrt (p ^ 2 + q ^ 2) - p) / q

theorem tpar_spec (p q x y : ℝ) (hpq : p ≠ 0 ∨ q ≠ 0) (h : p * x + q * y = 0) :
    (1 - tpar p q ^ 2) * x + 2 * tpar p q * y = 0 := by
  unfold tpar
  split_ifs with hq
  · have hp : p ≠ 0 := hpq.resolve_right (not_not.mpr hq)
    rw [hq, zero_mul, add_zero] at h
    have hx : x = 0 := (mul_eq_zero.mp h).resolve_left hp
    rw [hx]
    ring
  · have hr : Real.sqrt (p ^ 2 + q ^ 2) ^ 2 = p ^ 2 + q ^ 2 := Real.sq_sqrt (by positivity)
    generalize Real.sqrt (p ^ 2 + q ^ 2) = r at hr ⊢
    have H : (r - p) / q * q = r - p := div_mul_cancel₀ (r - p) hq
    generalize (r - p) / q = t at H ⊢
    have key : q ^ 2 * ((1 - t ^ 2) * x + 2 * t * y) = 0 := by
      linear_combination (-(t * q + (r - p)) * x + 2 * q * y) * H + (-x) * hr + 2 * (r - p) * h
    exact (mul_eq_zero.mp key).resolve_left (pow_ne_zero 2 hq)

theorem vec2_zero (u v : ℝ) : (![u, v] : Fin 2 → ℝ) 0 = u := rfl

theorem vec2_one (u v : ℝ) : (![u, v] : Fin 2 → ℝ) 1 = v := rfl

/-- **Theorem 5, split form** (all `n`): D-stability is Hurwitz stability together with the
absence of Lagrange points (b) and of tangency points (c) on the contact variety. -/
theorem dStable_iff_lagrange_tangency (a b : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (hb : ∀ i, 0 < b i) (A : Matrix (Fin n) (Fin n) ℝ) :
    DStable A ↔ HurwitzStable A ∧
      (¬ ∃ (d : Fin n → ℝ) (lam mu : ℝ), (∀ i, 0 < d i) ∧ contactPoly A d = 0 ∧
          ∀ i, a i * d i - b i =
            lam * (d i * (partialPoly A d i).re) + mu * (d i * (partialPoly A d i).im)) ∧
      (¬ ∃ (d : Fin n → ℝ) (t : ℝ), (∀ i, 0 < d i) ∧ contactPoly A d = 0 ∧
          ∀ i, (1 - t ^ 2) * (partialPoly A d i).re + 2 * t * (partialPoly A d i).im = 0) := by
  rw [dStable_iff_explicit a b ha hb A]
  apply and_congr_right
  intro _
  rw [← not_or]
  apply not_congr
  constructor
  · rintro ⟨d, hd, hc, Λ, Λ₀, hne, hΛeq⟩
    by_cases h0 : Λ₀ = 0
    · right
      subst h0
      have hpq : Λ 0 ≠ 0 ∨ Λ 1 ≠ 0 := by
        by_cases hp : Λ 0 = 0
        · right
          intro hq
          apply hne
          have hΛ : Λ = 0 := by
            funext j
            fin_cases j
            · exact hp
            · exact hq
          exact Prod.ext hΛ rfl
        · exact Or.inl hp
      refine ⟨d, tpar (Λ 0) (Λ 1), hd, hc, fun i => ?_⟩
      have h' := hΛeq i
      rw [zero_mul, add_zero] at h'
      exact tpar_spec (Λ 0) (Λ 1) _ _ hpq h'
    · left
      refine ⟨d, -Λ 0 / Λ₀, -Λ 1 / Λ₀, hd, hc, fun i => ?_⟩
      exact lagrange_fwd _ _ _ _ _ _ _ _ h0 (hd i).ne' (hΛeq i)
  · rintro (⟨d, lam, mu, hd, hc, hL⟩ | ⟨d, t, hd, hc, hT⟩)
    · refine ⟨d, hd, hc, ![-lam, -mu], 1, ?_, fun i => ?_⟩
      · intro h
        exact one_ne_zero (congrArg Prod.snd h : (1 : ℝ) = 0)
      · rw [vec2_zero, vec2_one]
        exact lagrange_bwd _ _ _ _ _ _ _ (hd i).ne' (hL i)
    · refine ⟨d, hd, hc, ![1 - t ^ 2, 2 * t], 0, ?_, fun i => ?_⟩
      · intro h
        have hΛ : (![1 - t ^ 2, 2 * t] : Fin 2 → ℝ) = 0 := congrArg Prod.fst h
        have e0 : 1 - t ^ 2 = 0 := by
          have h0 := congrFun hΛ 0
          rw [vec2_zero] at h0
          exact h0
        have e1 : 2 * t = 0 := by
          have h1 := congrFun hΛ 1
          rw [vec2_one] at h1
          exact h1
        have ht : t = 0 := by linarith
        rw [ht] at e0
        norm_num at e0
      · rw [vec2_zero, vec2_one, zero_mul, add_zero]
        exact hT i

/-! ### Weighted principal-minor sums -/

/-- `c_k(d) = ∑_{|S| = k} m_S ∏_{l ∈ S} d_l` with `m_S = det ((-A)[S])`. -/
def ck (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (d : Fin n → ℝ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card = k),
    minorR A S * ∏ l ∈ S, d l

/-- `c_k^{(i)}(d) = ∑_{|S| = k, i ∈ S} m_S ∏_{l ∈ S ∖ {i}} d_l` (the `d_i`-derivative of `c_k`). -/
def ckPart (A : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (d : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card = k ∧ i ∈ S),
    minorR A S * ∏ l ∈ S.erase i, d l

theorem cast_term (z : ℂ) (T : Finset (Fin n)) (d : Fin n → ℝ) (r : ℝ) :
    z * (∏ l ∈ T, (d l : ℂ)) * (r : ℂ) = z * ((r * ∏ l ∈ T, d l : ℝ) : ℂ) := by
  push_cast
  ring

theorem contactPoly_re_eq (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) :
    (contactPoly A d).re =
      ∑ S : Finset (Fin n), (Complex.I ^ (n - S.card)).re * (minorR A S * ∏ l ∈ S, d l) := by
  unfold contactPoly
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [pminor_eq_minorR, cast_term, Complex.re_mul_ofReal]

theorem contactPoly_im_eq (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) :
    (contactPoly A d).im =
      ∑ S : Finset (Fin n), (Complex.I ^ (n - S.card)).im * (minorR A S * ∏ l ∈ S, d l) := by
  unfold contactPoly
  rw [Complex.im_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [pminor_eq_minorR, cast_term, Complex.im_mul_ofReal]

theorem partialPoly_re_eq (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) (i : Fin n) :
    (partialPoly A d i).re = ∑ S : Finset (Fin n), if i ∈ S then
      (Complex.I ^ (n - S.card)).re * (minorR A S * ∏ l ∈ S.erase i, d l) else 0 := by
  unfold partialPoly
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  split_ifs
  · rw [pminor_eq_minorR, cast_term, Complex.re_mul_ofReal]
  · exact Complex.zero_re

theorem partialPoly_im_eq (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) (i : Fin n) :
    (partialPoly A d i).im = ∑ S : Finset (Fin n), if i ∈ S then
      (Complex.I ^ (n - S.card)).im * (minorR A S * ∏ l ∈ S.erase i, d l) else 0 := by
  unfold partialPoly
  rw [Complex.im_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  split_ifs
  · rw [pminor_eq_minorR, cast_term, Complex.im_mul_ofReal]
  · exact Complex.zero_im

theorem ck_zero (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) : ck A 0 d = 1 := by
  have hf : (Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card = 0) = {∅} := by
    ext S
    rw [Finset.mem_filter, Finset.mem_singleton, Finset.card_eq_zero]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  rw [ck, hf, Finset.sum_singleton, Finset.prod_empty, mul_one, minorR_empty]

theorem ckPart_zero (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) (i : Fin n) :
    ckPart A 0 d i = 0 := by
  unfold ckPart
  apply Finset.sum_eq_zero
  intro S hS
  rw [Finset.mem_filter, Finset.card_eq_zero] at hS
  obtain ⟨_, hS0, hi⟩ := hS
  rw [hS0] at hi
  exact absurd hi (Finset.notMem_empty i)

theorem filter_card_mem (i : Fin n) (k : ℕ) :
    ((Finset.univ : Finset (Finset (Fin n))).filter (fun S => i ∈ S)).filter
        (fun S => S.card = k) =
      (Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card = k ∧ i ∈ S) := by
  rw [Finset.filter_filter]
  exact Finset.filter_congr fun S _ => and_comm

/-! ### Powers of `i` for `n = 5` -/

theorem I_pow_five' : Complex.I ^ 5 = Complex.I := by
  linear_combination Complex.I * (Complex.I ^ 2 - 1) * Complex.I_sq

theorem card_le_five (S : Finset (Fin 5)) : S.card ≤ 5 :=
  (Finset.card_le_univ S).trans_eq (Fintype.card_fin 5)

theorem re_coeff_five (k : ℕ) (hk : k ≤ 5) (w : ℝ) :
    (Complex.I ^ (5 - k)).re * w =
      (if k = 1 then w else 0) - (if k = 3 then w else 0) + (if k = 5 then w else 0) := by
  interval_cases k
  · show (Complex.I ^ 5).re * w = _
    rw [I_pow_five']
    simp
  · show (Complex.I ^ 4).re * w = _
    rw [Complex.I_pow_four]
    simp
  · show (Complex.I ^ 3).re * w = _
    rw [Complex.I_pow_three]
    simp
  · show (Complex.I ^ 2).re * w = _
    rw [Complex.I_sq]
    simp
  · show (Complex.I ^ 1).re * w = _
    rw [pow_one]
    simp
  · show (Complex.I ^ 0).re * w = _
    rw [pow_zero]
    simp

theorem im_coeff_five (k : ℕ) (hk : k ≤ 5) (w : ℝ) :
    (Complex.I ^ (5 - k)).im * w =
      (if k = 0 then w else 0) - (if k = 2 then w else 0) + (if k = 4 then w else 0) := by
  interval_cases k
  · show (Complex.I ^ 5).im * w = _
    rw [I_pow_five']
    simp
  · show (Complex.I ^ 4).im * w = _
    rw [Complex.I_pow_four]
    simp
  · show (Complex.I ^ 3).im * w = _
    rw [Complex.I_pow_three]
    simp
  · show (Complex.I ^ 2).im * w = _
    rw [Complex.I_sq]
    simp
  · show (Complex.I ^ 1).im * w = _
    rw [pow_one]
    simp
  · show (Complex.I ^ 0).im * w = _
    rw [pow_zero]
    simp

theorem re_five_sum (s : Finset (Finset (Fin 5))) (w : Finset (Fin 5) → ℝ) :
    ∑ S ∈ s, (Complex.I ^ (5 - S.card)).re * w S =
      ∑ S ∈ s.filter (fun S => S.card = 1), w S - ∑ S ∈ s.filter (fun S => S.card = 3), w S +
        ∑ S ∈ s.filter (fun S => S.card = 5), w S := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun S _ => re_coeff_five S.card (card_le_five S) (w S)

theorem im_five_sum (s : Finset (Finset (Fin 5))) (w : Finset (Fin 5) → ℝ) :
    ∑ S ∈ s, (Complex.I ^ (5 - S.card)).im * w S =
      ∑ S ∈ s.filter (fun S => S.card = 0), w S - ∑ S ∈ s.filter (fun S => S.card = 2), w S +
        ∑ S ∈ s.filter (fun S => S.card = 4), w S := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun S _ => im_coeff_five S.card (card_le_five S) (w S)

/-! ### Explicit coefficients for `n = 5` -/

theorem contactPoly_re_five (A : Matrix (Fin 5) (Fin 5) ℝ) (d : Fin 5 → ℝ) :
    (contactPoly A d).re = ck A 1 d - ck A 3 d + ck A 5 d := by
  rw [contactPoly_re_eq, re_five_sum]
  rfl

theorem contactPoly_im_five (A : Matrix (Fin 5) (Fin 5) ℝ) (d : Fin 5 → ℝ) :
    (contactPoly A d).im = 1 - ck A 2 d + ck A 4 d := by
  rw [contactPoly_im_eq, im_five_sum]
  change ck A 0 d - ck A 2 d + ck A 4 d = _
  rw [ck_zero]

theorem partialPoly_re_five (A : Matrix (Fin 5) (Fin 5) ℝ) (d : Fin 5 → ℝ) (i : Fin 5) :
    (partialPoly A d i).re = ckPart A 1 d i - ckPart A 3 d i + ckPart A 5 d i := by
  rw [partialPoly_re_eq, ← Finset.sum_filter, re_five_sum, filter_card_mem, filter_card_mem,
    filter_card_mem]
  rfl

theorem partialPoly_im_five (A : Matrix (Fin 5) (Fin 5) ℝ) (d : Fin 5 → ℝ) (i : Fin 5) :
    (partialPoly A d i).im = -ckPart A 2 d i + ckPart A 4 d i := by
  rw [partialPoly_im_eq, ← Finset.sum_filter, im_five_sum, filter_card_mem, filter_card_mem,
    filter_card_mem]
  change ckPart A 0 d i - ckPart A 2 d i + ckPart A 4 d i = _
  rw [ckPart_zero, zero_sub]

theorem contactPoly_eq_zero_iff_five (A : Matrix (Fin 5) (Fin 5) ℝ) (d : Fin 5 → ℝ) :
    contactPoly A d = 0 ↔
      (ck A 1 d - ck A 3 d + ck A 5 d = 0 ∧ 1 - ck A 2 d + ck A 4 d = 0) := by
  rw [Complex.ext_iff, contactPoly_re_five, contactPoly_im_five, Complex.zero_re, Complex.zero_im]

/-- **The 5×5 D-stability criterion in explicit principal-minor polynomials.** -/
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
  rw [dStable_iff_lagrange_tangency a b ha hb A]
  simp only [contactPoly_eq_zero_iff_five, partialPoly_re_five, partialPoly_im_five, and_assoc,
    neg_add_eq_sub]

end DStability5x5

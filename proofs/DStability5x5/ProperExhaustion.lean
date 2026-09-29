module

public import proofs.DStability5x5.MorseCoverage

@[expose] public section

/-!
# Theorem M for an arbitrary proper exhaustion

`MorseCoverage.lean` proves Theorem M for `psi d = ∑ (d i + (d i)⁻¹)`.  Here the exhaustion is an
arbitrary function that is C¹ on the open orthant and has compact sublevel sets there
(`ProperExhaustion`).  Two weighted families are shown to qualify:

* `psiW a b d = ∑ (a i * d i + b i * (d i)⁻¹)`   (a, b > 0),
* `psiL a b d = ∑ (a i * d i - b i * Real.log (d i))` (a, b > 0, the log barrier used by the
  computational criterion; its Lagrange system has multihomogeneous Bézout number 1200 at n = 5).
-/

noncomputable section

open Matrix Filter Topology Set

namespace DStability5x5

open DUnstableCores DStabilityCharacterization.SpectralContinuation

variable {n : ℕ}

/-- A C¹ function on the open orthant with compact sublevel sets inside the orthant. -/
structure ProperExhaustion (n : ℕ) where
  f : (Fin n → ℝ) → ℝ
  smooth : ∀ d : Fin n → ℝ, (∀ i, 0 < d i) → ContDiffAt ℝ 1 f d
  proper : ∀ R : ℝ, ∃ K : Set (Fin n → ℝ), IsCompact K ∧ (∀ d ∈ K, ∀ i, 0 < d i) ∧
    ∀ d : Fin n → ℝ, (∀ i, 0 < d i) → f d ≤ R → d ∈ K

/-- Fritz-John critical points of an exhaustion `ψ` on Johnson's contact variety. -/
def MorseCriticalFor (ψ : ProperExhaustion n) (A : Matrix (Fin n) (Fin n) ℝ)
    (d : Fin n → ℝ) : Prop :=
  (∀ i, 0 < d i) ∧ contactDet A d = 0 ∧
    ∃ Λ : Fin 2 → ℝ, ∃ Λ₀ : ℝ, (Λ, Λ₀) ≠ 0 ∧
      Λ 0 • fderiv ℝ (contactRe A) d + Λ 1 • fderiv ℝ (contactIm A) d +
        Λ₀ • fderiv ℝ ψ.f d = 0

theorem exists_morseCriticalFor_of_contact (ψ : ProperExhaustion n)
    (A : Matrix (Fin n) (Fin n) ℝ) {d₀ : Fin n → ℝ}
    (hd₀ : ∀ i, 0 < d₀ i) (hc : contactDet A d₀ = 0) : ∃ d, MorseCriticalFor ψ A d := by
  obtain ⟨K, hKc, hKpos, hKsub⟩ := ψ.proper (ψ.f d₀)
  let K' : Set (Fin n → ℝ) := K ∩ {d | contactDet A d = 0}
  have hK'c : IsCompact K' :=
    hKc.inter_right (isClosed_eq (contactDet_contDiff A).continuous continuous_const)
  have hd₀K : d₀ ∈ K' := ⟨hKsub d₀ hd₀ (le_refl _), hc⟩
  have hcont : ContinuousOn ψ.f K' := by
    intro d hd
    exact (ψ.smooth d (hKpos d hd.1)).continuousAt.continuousWithinAt
  obtain ⟨dstar, hdK, hmin⟩ := hK'c.exists_isMinOn ⟨d₀, hd₀K⟩ hcont
  have hpos : ∀ i, 0 < dstar i := hKpos dstar hdK.1
  have hle : ψ.f dstar ≤ ψ.f d₀ := hmin hd₀K
  let f : Fin 2 → (Fin n → ℝ) → ℝ := ![contactRe A, contactIm A]
  have hdstar0 : contactDet A dstar = 0 := hdK.2
  have hS : ∀ x, (∀ i, f i x = f i dstar) → contactDet A x = 0 := by
    intro x hx
    have h0 := hx 0
    have h1 := hx 1
    simp only [f, Matrix.cons_val_zero, Matrix.cons_val_one, contactRe, contactIm,
      hdstar0, Complex.zero_re, Complex.zero_im] at h0 h1
    exact Complex.ext h0 h1
  have hloc : IsLocalMinOn ψ.f {x | ∀ i, f i x = f i dstar} dstar := by
    have hO : {x : Fin n → ℝ | ∀ i, 0 < x i} ∈ 𝓝 dstar := by
      have hopen : IsOpen {x : Fin n → ℝ | ∀ i, 0 < x i} := by
        have hEq : {x : Fin n → ℝ | ∀ i, 0 < x i} = Set.pi Set.univ (fun _ => Set.Ioi 0) := by
          ext x
          simp
        rw [hEq]
        exact isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioi)
      exact hopen.mem_nhds hpos
    filter_upwards [mem_nhdsWithin_of_mem_nhds hO, self_mem_nhdsWithin] with x hxpos hxS
    have hxc : contactDet A x = 0 := hS x hxS
    by_cases hx : ψ.f x ≤ ψ.f d₀
    · exact hmin ⟨hKsub x hxpos hx, hxc⟩
    · push Not at hx
      show ψ.f dstar ≤ ψ.f x
      linarith
  have hf' : ∀ i, HasStrictFDerivAt (f i) (fderiv ℝ (f i) dstar) dstar := by
    intro i
    fin_cases i
    · show HasStrictFDerivAt (contactRe A) (fderiv ℝ (contactRe A) dstar) dstar
      exact ((contactRe_contDiff A).contDiffAt).hasStrictFDerivAt one_ne_zero
    · show HasStrictFDerivAt (contactIm A) (fderiv ℝ (contactIm A) dstar) dstar
      exact ((contactIm_contDiff A).contDiffAt).hasStrictFDerivAt one_ne_zero
  have hφ' : HasStrictFDerivAt ψ.f (fderiv ℝ ψ.f dstar) dstar :=
    (ψ.smooth dstar hpos).hasStrictFDerivAt one_ne_zero
  obtain ⟨Λ, Λ₀, hne, hsum⟩ :=
    IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt (Or.inl hloc) hf' hφ'
  refine ⟨dstar, hpos, hdstar0, Λ, Λ₀, hne, ?_⟩
  simpa [Fin.sum_univ_two, f] using hsum

/-- **Theorem M for any proper exhaustion.** -/
theorem dStable_iff_morseFor (ψ : ProperExhaustion n) (A : Matrix (Fin n) (Fin n) ℝ) :
    DStable A ↔ HurwitzStable A ∧ ¬ ∃ d, MorseCriticalFor ψ A d := by
  constructor
  · intro hA
    refine ⟨by simpa using hA (fun _ => 1) (fun _ => one_pos), ?_⟩
    rintro ⟨d, hd, hc, -⟩
    obtain ⟨v, hv⟩ := (contact_iff_eigenpair A d).mp hc
    have h := hA d hd Complex.I v hv
    simp at h
  · rintro ⟨hH, hno⟩
    apply dStable_of_no_axis_of_one_scaling A (fun _ => 1) (fun _ => one_pos)
      (by simpa using hH)
    intro d hd z v hv hz
    obtain ⟨d', hd', hc'⟩ := contact_of_axis A hH d hd z v hv hz
    exact hno (exists_morseCriticalFor_of_contact ψ A hd' hc')

/-! ## Two weighted families of proper exhaustions -/

/-- Weighted reciprocal exhaustion. -/
def psiW (a b : Fin n → ℝ) (d : Fin n → ℝ) : ℝ := ∑ i, (a i * d i + b i * (d i)⁻¹)

/-- Weighted log barrier. -/
def psiL (a b : Fin n → ℝ) (d : Fin n → ℝ) : ℝ := ∑ i, (a i * d i - b i * Real.log (d i))

theorem psiW_term_pos {a b : Fin n → ℝ} (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    {x : Fin n → ℝ} (hx : ∀ i, 0 < x i) (i : Fin n) : 0 < a i * x i + b i * (x i)⁻¹ := by
  have := ha i; have := hb i; have := hx i; positivity

theorem psiL_term_ge {a b : Fin n → ℝ} (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    {t : ℝ} (ht : 0 < t) (i : Fin n) :
    b i * (1 - Real.log (b i / a i)) ≤ a i * t - b i * Real.log t := by
  -- a t - b log t is minimized at t = b/a with value b - b log(b/a)
  have hai := ha i
  have hbi := hb i
  have hba : 0 < b i / a i := div_pos hbi hai
  have key : Real.log (t / (b i / a i)) ≤ t / (b i / a i) - 1 :=
    Real.log_le_sub_one_of_pos (div_pos ht hba)
  rw [Real.log_div (ne_of_gt ht) (ne_of_gt hba)] at key
  have h1 : t / (b i / a i) = a i * t / b i := by field_simp
  rw [h1] at key
  have h2 : b i * (Real.log t - Real.log (b i / a i)) ≤ b i * (a i * t / b i - 1) :=
    mul_le_mul_of_nonneg_left key hbi.le
  have h3 : b i * (a i * t / b i - 1) = a i * t - b i := by field_simp
  nlinarith [h2, h3]

theorem psiW_contDiffAt (a b : Fin n → ℝ) {d : Fin n → ℝ} (hd : ∀ i, 0 < d i) :
    ContDiffAt ℝ 1 (psiW a b) d := by
  unfold psiW
  apply ContDiffAt.sum
  intro i _
  have h1 : ContDiffAt ℝ 1 (fun x : Fin n → ℝ => x i) d := (contDiff_apply ℝ ℝ i).contDiffAt
  have h2 : ContDiffAt ℝ 1 (fun x : Fin n → ℝ => (x i)⁻¹) d :=
    (contDiffAt_inv ℝ (ne_of_gt (hd i))).comp d h1
  exact (contDiffAt_const.mul h1).add (contDiffAt_const.mul h2)

theorem psiL_contDiffAt (a b : Fin n → ℝ) {d : Fin n → ℝ} (hd : ∀ i, 0 < d i) :
    ContDiffAt ℝ 1 (psiL a b) d := by
  unfold psiL
  apply ContDiffAt.sum
  intro i _
  have h1 : ContDiffAt ℝ 1 (fun x : Fin n → ℝ => x i) d := (contDiff_apply ℝ ℝ i).contDiffAt
  have h2 : ContDiffAt ℝ 1 (fun x : Fin n → ℝ => Real.log (x i)) d :=
    h1.log (ne_of_gt (hd i))
  exact (contDiffAt_const.mul h1).sub (contDiffAt_const.mul h2)

/-- The weighted reciprocal exhaustion is proper. -/
def psiWExhaustion (a b : Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    ProperExhaustion n where
  f := psiW a b
  smooth := fun d hd => psiW_contDiffAt a b hd
  proper := by
    intro R
    set Rp := max R 1 with hRp
    have hRppos : 0 < Rp := lt_of_lt_of_le one_pos (le_max_right R 1)
    refine ⟨Set.pi Set.univ (fun i => Set.Icc (b i / Rp) (Rp / a i)),
      isCompact_univ_pi (fun _ => isCompact_Icc), ?_, ?_⟩
    · intro d hd i
      have h := (hd i (Set.mem_univ i)).1
      exact lt_of_lt_of_le (div_pos (hb i) hRppos) h
    · intro d hd hR i _
      have hterm : a i * d i + b i * (d i)⁻¹ ≤ Rp := by
        have hle : a i * d i + b i * (d i)⁻¹ ≤ psiW a b d := by
          unfold psiW
          exact Finset.single_le_sum (f := fun j => a j * d j + b j * (d j)⁻¹)
            (fun j _ => (psiW_term_pos ha hb hd j).le) (Finset.mem_univ i)
        exact le_trans hle (le_trans hR (le_max_left R 1))
      have hai := ha i
      have hbi := hb i
      have hdi := hd i
      have hinv : 0 < (d i)⁻¹ := inv_pos.mpr hdi
      have p1 : 0 < a i * d i := mul_pos hai hdi
      have p2 : 0 < b i * (d i)⁻¹ := mul_pos hbi hinv
      constructor
      · rw [div_le_iff₀ hRppos]
        have : b i * (d i)⁻¹ ≤ Rp := by linarith
        have h3 : b i ≤ Rp * d i := by
          have := mul_le_mul_of_nonneg_right this hdi.le
          rwa [mul_assoc, inv_mul_cancel₀ (ne_of_gt hdi), mul_one] at this
        linarith [mul_comm (d i) Rp]
      · rw [le_div_iff₀ hai]
        linarith [mul_comm (d i) (a i)]

/-- The weighted log barrier is proper. -/
def psiLExhaustion (a b : Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    ProperExhaustion n where
  f := psiL a b
  smooth := fun d hd => psiL_contDiffAt a b hd
  proper := by
    intro R
    let m : Fin n → ℝ := fun j => b j * (1 - Real.log (b j / a j))
    let R' : ℝ := R + ∑ j, |m j|
    refine ⟨Set.pi Set.univ (fun i => Set.Icc (Real.exp (-(R' / b i)))
      (2 * (R' - b i + b i * Real.log (2 * b i / a i)) / a i)),
      isCompact_univ_pi (fun _ => isCompact_Icc), ?_, ?_⟩
    · intro d hd i
      exact lt_of_lt_of_le (Real.exp_pos _) (hd i (Set.mem_univ i)).1
    · intro d hd hR i _
      have hai := ha i
      have hbi := hb i
      have hdi := hd i
      -- the i-th term is at most R'
      have hterm : a i * d i - b i * Real.log (d i) ≤ R' := by
        have hsplit : psiL a b d = (a i * d i - b i * Real.log (d i)) +
            ∑ j ∈ Finset.univ.erase i, (a j * d j - b j * Real.log (d j)) := by
          unfold psiL
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
        have hrest : -(∑ j, |m j|) ≤ ∑ j ∈ Finset.univ.erase i, (a j * d j - b j * Real.log (d j)) := by
          have h1 : ∑ j ∈ Finset.univ.erase i, (-|m j|) ≤
              ∑ j ∈ Finset.univ.erase i, (a j * d j - b j * Real.log (d j)) := by
            apply Finset.sum_le_sum
            intro j _
            exact le_trans (neg_abs_le (m j)) (psiL_term_ge ha hb (hd j) j)
          have h2 : ∑ j ∈ Finset.univ.erase i, |m j| ≤ ∑ j, |m j| :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
              (fun j _ _ => abs_nonneg (m j))
          rw [Finset.sum_neg_distrib] at h1
          linarith
        linarith
      constructor
      · -- lower bound: -b log t ≤ a t - b log t ≤ R'
        have hlog : -(R' / b i) ≤ Real.log (d i) := by
          have h4 : -(b i * Real.log (d i)) ≤ R' := by nlinarith [mul_pos hai hdi]
          have h5 : -Real.log (d i) ≤ R' / b i := by
            rw [le_div_iff₀ hbi]
            have h6 : -Real.log (d i) * b i = -(b i * Real.log (d i)) := by ring
            linarith
          linarith
        calc Real.exp (-(R' / b i)) ≤ Real.exp (Real.log (d i)) := Real.exp_le_exp.mpr hlog
          _ = d i := Real.exp_log hdi
      · -- upper bound via log t ≤ a t / (2b) - 1 + log(2b/a)
        have hc : 0 < 2 * b i / a i := by positivity
        have hx : 0 < d i / (2 * b i / a i) := div_pos hdi hc
        have key := Real.log_le_sub_one_of_pos hx
        rw [Real.log_div (ne_of_gt hdi) (ne_of_gt hc)] at key
        have h1 : d i / (2 * b i / a i) = a i * d i / (2 * b i) := by field_simp
        rw [h1] at key
        have h2 : b i * Real.log (d i) ≤ b i * (a i * d i / (2 * b i) - 1 + Real.log (2 * b i / a i)) := by
          apply mul_le_mul_of_nonneg_left _ hbi.le
          linarith
        have h3 : b i * (a i * d i / (2 * b i) - 1 + Real.log (2 * b i / a i)) =
            a i * d i / 2 - b i + b i * Real.log (2 * b i / a i) := by
          field_simp
        rw [le_div_iff₀ hai]
        nlinarith [h2, h3]

/-- Theorem M with the weighted log barrier (the exhaustion used by the computational criterion). -/
theorem dStable_iff_morse_logBarrier (a b : Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    DStable A ↔ HurwitzStable A ∧ ¬ ∃ d, MorseCriticalFor (psiLExhaustion a b ha hb) A d :=
  dStable_iff_morseFor _ A

/-- Theorem M with the weighted reciprocal exhaustion. -/
theorem dStable_iff_morse_recip (a b : Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    DStable A ↔ HurwitzStable A ∧ ¬ ∃ d, MorseCriticalFor (psiWExhaustion a b ha hb) A d :=
  dStable_iff_morseFor _ A

end DStability5x5

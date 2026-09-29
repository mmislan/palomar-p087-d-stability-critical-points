module

public import proofs.DStabilityCharacterization.SpectralContinuation

@[expose] public section

/-!
# Morse coverage for D-stability (Theorem M)

For a real `n × n` matrix `A` and positive rates `d`, Johnson's contact determinant is
`contactDet A d = det (i • 1 - A · diag d)`; it vanishes exactly when `A · diag d` has the
eigenvalue `i`.  With the proper exhaustion `psi d = ∑ (d i + (d i)⁻¹)` of the open orthant,
a *Morse-critical point* is a positive contact at which the derivatives of `Re contactDet`,
`Im contactDet` and `psi` are linearly dependent (Fritz John form of the Lagrange condition).

Main theorem (`dStable_iff_morse`):

  `DStable A ↔ HurwitzStable A ∧ ¬ ∃ d, MorseCritical A d`.

The proof needs no stratum (time-scale limit) analysis and no module hypothesis: the contact
set is closed in the open orthant, `psi` has compact sublevel sets there, so a nonempty contact
set carries a `psi`-minimizer, and the Lagrange multiplier theorem makes it Morse-critical.
-/

noncomputable section

open Matrix Filter Topology Set
open scoped ComplexConjugate

namespace DStability5x5

open DUnstableCores DStabilityCharacterization.SpectralContinuation

variable {n : ℕ}

/-- Johnson's contact determinant `det (i • 1 - A · diag d)` (right scaling). -/
def contactDet (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) : ℂ :=
  (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ) - complexify (rightScale A d)).det

/-- Real part of the contact determinant. -/
def contactRe (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) : ℝ := (contactDet A d).re

/-- Imaginary part of the contact determinant. -/
def contactIm (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) : ℝ := (contactDet A d).im

/-- A proper exhaustion of the open positive orthant. -/
def psi (d : Fin n → ℝ) : ℝ := ∑ i, (d i + (d i)⁻¹)

/-- Fritz-John critical points of `psi` on Johnson's contact variety. -/
def MorseCritical (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) : Prop :=
  (∀ i, 0 < d i) ∧ contactDet A d = 0 ∧
    ∃ Λ : Fin 2 → ℝ, ∃ Λ₀ : ℝ, (Λ, Λ₀) ≠ 0 ∧
      Λ 0 • fderiv ℝ (contactRe A) d + Λ 1 • fderiv ℝ (contactIm A) d +
        Λ₀ • fderiv ℝ psi d = 0

/-! ## Smoothness -/

theorem contactDet_contDiff (A : Matrix (Fin n) (Fin n) ℝ) :
    ContDiff ℝ 1 (contactDet A) := by
  unfold contactDet
  simp_rw [Matrix.det_apply]
  apply ContDiff.sum
  intro σ _
  simp only [Units.smul_def, zsmul_eq_mul]
  apply ContDiff.mul contDiff_const
  apply contDiff_prod
  intro i _
  simp only [Matrix.sub_apply, Matrix.smul_apply, complexify, rightScale]
  apply ContDiff.sub contDiff_const
  have h : ContDiff ℝ 1 (fun d : Fin n → ℝ => A (σ i) i * d i) :=
    contDiff_const.mul (contDiff_apply ℝ ℝ i)
  exact Complex.ofRealCLM.contDiff.comp h

theorem contactRe_contDiff (A : Matrix (Fin n) (Fin n) ℝ) :
    ContDiff ℝ 1 (contactRe A) :=
  Complex.reCLM.contDiff.comp (contactDet_contDiff A)

theorem contactIm_contDiff (A : Matrix (Fin n) (Fin n) ℝ) :
    ContDiff ℝ 1 (contactIm A) :=
  Complex.imCLM.contDiff.comp (contactDet_contDiff A)

theorem psi_contDiffAt {d : Fin n → ℝ} (hd : ∀ i, 0 < d i) :
    ContDiffAt ℝ 1 psi d := by
  unfold psi
  apply ContDiffAt.sum
  intro i _
  have h1 : ContDiffAt ℝ 1 (fun x : Fin n → ℝ => x i) d := (contDiff_apply ℝ ℝ i).contDiffAt
  have h2 : ContDiffAt ℝ 1 (fun x : Fin n → ℝ => (x i)⁻¹) d :=
    (contDiffAt_inv ℝ (ne_of_gt (hd i))).comp d h1
  exact h1.add h2

theorem psi_continuousOn_pos :
    ContinuousOn (psi : (Fin n → ℝ) → ℝ) {d | ∀ i, 0 < d i} := by
  intro d hd
  exact (psi_contDiffAt hd).continuousAt.continuousWithinAt

/-! ## Elementary bounds on `psi` -/

theorem term_le_psi {x : Fin n → ℝ} (hx : ∀ i, 0 < x i) (i : Fin n) :
    x i + (x i)⁻¹ ≤ psi x := by
  unfold psi
  exact Finset.single_le_sum (f := fun j => x j + (x j)⁻¹)
    (fun j _ => by have := hx j; positivity) (Finset.mem_univ i)

theorem mem_box_of_psi_le {x : Fin n → ℝ} (hx : ∀ i, 0 < x i) {R : ℝ} (hR : psi x ≤ R)
    (i : Fin n) : R⁻¹ ≤ x i ∧ x i ≤ R := by
  have ht := term_le_psi hx i
  have hxi := hx i
  have hinv : 0 < (x i)⁻¹ := inv_pos.mpr hxi
  constructor
  · have h1 : (x i)⁻¹ ≤ R := by linarith
    have hRpos : 0 < R := by linarith
    calc R⁻¹ ≤ ((x i)⁻¹)⁻¹ := by
          exact inv_anti₀ hinv h1
      _ = x i := inv_inv (x i)
  · linarith

/-! ## Contacts and eigenpairs -/

theorem contact_iff_eigenpair (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) :
    contactDet A d = 0 ↔ ∃ v, HasEigenpair (rightScale A d) Complex.I v := by
  unfold contactDet
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨v, hv0, hv⟩
    refine ⟨v, hv0, fun i => ?_⟩
    have := congrFun hv i
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    linear_combination -this
  · rintro ⟨v, hv0, hv⟩
    refine ⟨v, hv0, funext fun i => ?_⟩
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [hv i]
    ring

theorem eigenpair_rescale (A : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) (c : ℝ) (z : ℂ)
    (v : Fin n → ℂ) (h : HasEigenpair (rightScale A d) z v) :
    HasEigenpair (rightScale A (fun i => c * d i)) ((c : ℂ) * z) v := by
  refine ⟨h.1, fun i => ?_⟩
  have hi := h.2 i
  simp only [Matrix.mulVec, dotProduct, complexify, rightScale] at hi ⊢
  have : ∑ j, ((A i j * (c * d j) : ℝ) : ℂ) * v j = (c : ℂ) * ∑ j, ((A i j * d j : ℝ) : ℂ) * v j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  rw [this, hi]
  ring

theorem eigenpair_conj (M : Matrix (Fin n) (Fin n) ℝ) (z : ℂ) (v : Fin n → ℂ)
    (h : HasEigenpair M z v) :
    HasEigenpair M (conj z) (fun i => conj (v i)) := by
  refine ⟨fun h0 => h.1 ?_, fun i => ?_⟩
  · funext i
    have := congrFun h0 i
    simpa using this
  · have hi := h.2 i
    simp only [Matrix.mulVec, dotProduct, complexify] at hi ⊢
    have : ∑ j, (M i j : ℂ) * conj (v j) = conj (∑ j, (M i j : ℂ) * v j) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, Complex.conj_ofReal]
    rw [this, hi, map_mul]

theorem no_zero_eigen_of_hurwitz (A : Matrix (Fin n) (Fin n) ℝ) (hA : HurwitzStable A)
    (d : Fin n → ℝ) (hd : ∀ i, 0 < d i) (v : Fin n → ℂ) :
    ¬ HasEigenpair (rightScale A d) 0 v := by
  rintro ⟨hv0, hv⟩
  let w : Fin n → ℂ := fun j => (d j : ℂ) * v j
  have hw0 : w ≠ 0 := by
    intro hw
    apply hv0
    funext j
    have := congrFun hw j
    simp only [w, Pi.zero_apply, mul_eq_zero, Complex.ofReal_eq_zero] at this
    rcases this with h | h
    · exact absurd h (ne_of_gt (hd j))
    · simpa using h
  have hw : HasEigenpair A 0 w := by
    refine ⟨hw0, fun i => ?_⟩
    have hi := hv i
    simp only [Matrix.mulVec, dotProduct, complexify, rightScale, zero_mul] at hi ⊢
    rw [← hi]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [w]
    push_cast
    ring
  have := hA 0 w hw
  simp at this

/-- An imaginary-axis eigenvalue of a positive scaling produces a positive contact. -/
theorem contact_of_axis (A : Matrix (Fin n) (Fin n) ℝ) (hA : HurwitzStable A)
    (d : Fin n → ℝ) (hd : ∀ i, 0 < d i) (z : ℂ) (v : Fin n → ℂ)
    (hv : HasEigenpair (rightScale A d) z v) (hz : z.re = 0) :
    ∃ d' : Fin n → ℝ, (∀ i, 0 < d' i) ∧ contactDet A d' = 0 := by
  have key : ∀ (z : ℂ) (v : Fin n → ℂ), HasEigenpair (rightScale A d) z v → z.re = 0 →
      0 < z.im → ∃ d' : Fin n → ℝ, (∀ i, 0 < d' i) ∧ contactDet A d' = 0 := by
    intro z v hv hz him
    refine ⟨fun i => (z.im)⁻¹ * d i, fun i => mul_pos (inv_pos.mpr him) (hd i), ?_⟩
    rw [contact_iff_eigenpair]
    refine ⟨v, ?_⟩
    have h := eigenpair_rescale A d (z.im)⁻¹ z v hv
    have hz' : (((z.im)⁻¹ : ℝ) : ℂ) * z = Complex.I := by
      apply Complex.ext
      · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hz, Complex.I_re]
        ring
      · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hz, Complex.I_im]
        field_simp
        norm_num
    rw [hz'] at h
    exact h
  rcases lt_trichotomy z.im 0 with him | him | him
  · have hc := eigenpair_conj _ z v hv
    exact key (conj z) _ hc (by simpa using hz) (by simpa using him)
  · exfalso
    have hz0 : z = 0 := Complex.ext hz him
    subst hz0
    exact no_zero_eigen_of_hurwitz A hA d hd v hv
  · exact key z v hv hz him

/-! ## The minimizer and the multiplier theorem -/

theorem exists_morseCritical_of_contact (A : Matrix (Fin n) (Fin n) ℝ) {d₀ : Fin n → ℝ}
    (hd₀ : ∀ i, 0 < d₀ i) (hc : contactDet A d₀ = 0) : ∃ d, MorseCritical A d := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      exfalso
      have h1 : contactDet A d₀ = 1 := by
        unfold contactDet
        exact Matrix.det_isEmpty
      rw [h1] at hc
      exact one_ne_zero hc
    · exact h
  set R := psi d₀ with hRdef
  have hRpos : 0 < R := by
    have h0 := term_le_psi hd₀ ⟨0, hn⟩
    have h1 := hd₀ ⟨0, hn⟩
    have h2 : 0 < (d₀ ⟨0, hn⟩)⁻¹ := inv_pos.mpr h1
    linarith
  let box : Set (Fin n → ℝ) := Set.pi Set.univ (fun _ => Set.Icc R⁻¹ R)
  let K : Set (Fin n → ℝ) := box ∩ {d | contactDet A d = 0}
  have hbox_pos : ∀ d ∈ box, ∀ i, 0 < d i := by
    intro d hd i
    have h := (hd i (Set.mem_univ i)).1
    exact lt_of_lt_of_le (inv_pos.mpr hRpos) h
  have hKc : IsCompact K :=
    (isCompact_univ_pi (fun _ => isCompact_Icc)).inter_right
      (isClosed_eq (contactDet_contDiff A).continuous continuous_const)
  have hd₀K : d₀ ∈ K := ⟨fun i _ => mem_box_of_psi_le hd₀ (le_refl R) i, hc⟩
  have hcont : ContinuousOn psi K :=
    psi_continuousOn_pos.mono (fun d hd => hbox_pos d hd.1)
  obtain ⟨dstar, hdK, hmin⟩ := hKc.exists_isMinOn ⟨d₀, hd₀K⟩ hcont
  have hpos : ∀ i, 0 < dstar i := hbox_pos dstar hdK.1
  have hpsi_le : psi dstar ≤ R := hmin hd₀K
  let f : Fin 2 → (Fin n → ℝ) → ℝ := ![contactRe A, contactIm A]
  have hdstar0 : contactDet A dstar = 0 := hdK.2
  have hS : ∀ x, (∀ i, f i x = f i dstar) → contactDet A x = 0 := by
    intro x hx
    have h0 := hx 0
    have h1 := hx 1
    simp only [f, Matrix.cons_val_zero, Matrix.cons_val_one, contactRe, contactIm,
      hdstar0, Complex.zero_re, Complex.zero_im] at h0 h1
    exact Complex.ext h0 h1
  have hloc : IsLocalMinOn psi {x | ∀ i, f i x = f i dstar} dstar := by
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
    by_cases hxb : x ∈ box
    · exact hmin ⟨hxb, hxc⟩
    · have hex : ∃ i, ¬ (R⁻¹ ≤ x i ∧ x i ≤ R) := by
        by_contra h
        push Not at h
        exact hxb (fun i _ => h i)
      obtain ⟨i, hi⟩ := hex
      have hterm := term_le_psi hxpos i
      have hxi := hxpos i
      have hinv : 0 < (x i)⁻¹ := inv_pos.mpr hxi
      have hgt : R < x i + (x i)⁻¹ := by
        by_cases h1 : R⁻¹ ≤ x i
        · have h2 : R < x i := by
            by_contra h3
            push Not at h3
            exact hi ⟨h1, h3⟩
          linarith
        · push Not at h1
          have h4 : R < (x i)⁻¹ := (lt_inv_comm₀ hRpos hxi).mpr h1
          linarith
      show psi dstar ≤ psi x
      linarith
  have hf' : ∀ i, HasStrictFDerivAt (f i) (fderiv ℝ (f i) dstar) dstar := by
    intro i
    fin_cases i
    · show HasStrictFDerivAt (contactRe A) (fderiv ℝ (contactRe A) dstar) dstar
      exact ((contactRe_contDiff A).contDiffAt).hasStrictFDerivAt one_ne_zero
    · show HasStrictFDerivAt (contactIm A) (fderiv ℝ (contactIm A) dstar) dstar
      exact ((contactIm_contDiff A).contDiffAt).hasStrictFDerivAt one_ne_zero
  have hφ' : HasStrictFDerivAt psi (fderiv ℝ psi dstar) dstar :=
    (psi_contDiffAt hpos).hasStrictFDerivAt one_ne_zero
  obtain ⟨Λ, Λ₀, hne, hsum⟩ :=
    IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt (Or.inl hloc) hf' hφ'
  refine ⟨dstar, hpos, hdstar0, Λ, Λ₀, hne, ?_⟩
  simpa [Fin.sum_univ_two, f] using hsum

/-! ## Theorem M -/

/-- **Theorem M (Morse coverage).**  A real square matrix is D-stable iff it is Hurwitz and
the psi-critical set of Johnson's contact variety has no positive point. -/
theorem dStable_iff_morse (A : Matrix (Fin n) (Fin n) ℝ) :
    DStable A ↔ HurwitzStable A ∧ ¬ ∃ d, MorseCritical A d := by
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
    exact hno (exists_morseCritical_of_contact A hd' hc')

end DStability5x5

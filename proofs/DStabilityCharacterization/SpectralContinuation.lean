module

public import proofs.DUnstableCores.BlockTriangular

@[expose] public section

/-! Spectral continuation in literal finite-matrix eigenpair semantics. -/
noncomputable section
open Filter Topology Set
open scoped Matrix.Norms.Operator
namespace DStabilityCharacterization.SpectralContinuation
open DUnstableCores

theorem root_near_of_eval_small (p : Polynomial ℂ) (hp : p.Monic)
    (z : ℂ) (ε : ℝ) (hε : 0 < ε)
    (hsmall : ‖p.eval z‖ < ε ^ p.natDegree) :
    ∃ w ∈ p.roots, ‖z-w‖ < ε := by
  by_contra! h
  have hs := IsAlgClosed.splits p
  have hb := Multiset.prod_map_le_prod_map₀ (fun _ : ℂ => ε)
    (fun w => ‖z-w‖) (by intros; exact hε.le) h
  have he : ‖p.eval z‖ = (p.roots.map (fun w => ‖z-w‖)).prod := by
    rw [hs.eval_eq_prod_roots_of_monic hp]
    exact (p.roots.prod_hom' (NormedField.toMulRingNorm ℂ) (fun w => z-w)).symm
  rw [he] at hsmall
  have hb' : ε ^ p.natDegree ≤ (p.roots.map (fun w => ‖z-w‖)).prod := by
    simpa [Multiset.map_const', Multiset.prod_replicate,
      ← hs.natDegree_eq_card_roots] using hb
  exact not_lt_of_ge hb' hsmall

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stable_iff_spectrum (A : Matrix ι ι ℝ) :
    HurwitzStable A ↔ spectrum ℂ (complexify A) ⊆ {z : ℂ | z.re < 0} := by
  constructor
  · intro h z hz
    obtain ⟨v, hv⟩ := isRoot_complexified_charpoly_yields_eigenpair A z
      (Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz)
    exact h z v hv
  · intro h z v hv
    exact h (Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hv.isRoot_charpoly)

omit [Fintype ι] [DecidableEq ι] in
@[fun_prop] theorem continuous_complexify : Continuous (complexify : Matrix ι ι ℝ → Matrix ι ι ℂ) := by
  unfold complexify
  fun_prop

theorem isOpen_hurwitzStable : IsOpen {A : Matrix ι ι ℝ | HurwitzStable A} := by
  rw [isOpen_iff_mem_nhds]
  intro A hA
  have hopen : IsOpen {z : ℂ | z.re < 0} := isOpen_lt Complex.continuous_re continuous_const
  have hu := (upperHemicontinuous_spectrum ℂ (Matrix ι ι ℂ)).comp
    continuous_complexify
  have ht := hu A {z : ℂ | z.re < 0}
    (hopen.mem_nhdsSet.mpr ((stable_iff_spectrum A).mp hA))
  filter_upwards [ht] with B hB
  exact (stable_iff_spectrum B).mpr (hopen.mem_nhdsSet.mp hB)

theorem isOpen_hurwitzUnstable : IsOpen {A : Matrix ι ι ℝ | HurwitzUnstable A} := by
  rw [isOpen_iff_mem_nhds]
  rintro A ⟨z, v, hz, hv⟩
  have hcont : Continuous (fun B : Matrix ι ι ℝ => ‖(complexify B).charpoly.eval z‖) := by
    simp_rw [Matrix.eval_charpoly]
    fun_prop
  have heps : 0 < (z.re/2) ^ Fintype.card ι := pow_pos (by linarith) _
  have hsmall : ‖(complexify A).charpoly.eval z‖ < (z.re/2) ^ Fintype.card ι := by
    rw [hv.isRoot_charpoly.eq_zero, norm_zero]
    exact heps
  have hn := (isOpen_lt hcont continuous_const).mem_nhds hsmall
  filter_upwards [hn] with B hB
  obtain ⟨w, hw, hdist⟩ := root_near_of_eval_small (complexify B).charpoly
    (Matrix.charpoly_monic _) z (z.re/2) (by linarith)
    (by simpa [Matrix.charpoly_natDegree_eq_dim] using hB)
  obtain ⟨u, hu⟩ := isRoot_complexified_charpoly_yields_eigenpair B w
    ((Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).mp hw)
  refine ⟨w, u, ?_, hu⟩
  have hreal := Complex.re_le_norm (z-w)
  simp only [Complex.sub_re] at hreal
  linarith

/-- On any connected parameter set, exclusion of imaginary eigenvalues and one
Hurwitz base point force Hurwitz stability throughout. No root-continuity
hypothesis is imposed on the caller. -/
theorem hurwitzStable_on_preconnected {α : Type*} [TopologicalSpace α]
    (S : Set α) (hS : IsPreconnected S) (A : α → Matrix ι ι ℝ)
    (hA : ContinuousOn A S)
    (haxis : ∀ t ∈ S, ∀ z v, HasEigenpair (A t) z v → z.re ≠ 0)
    (t₀ : α) (ht₀ : t₀ ∈ S) (hbase : HurwitzStable (A t₀)) :
    ∀ t ∈ S, HurwitzStable (A t) := by
  have himg := hS.image A hA
  have hdis : Disjoint {B : Matrix ι ι ℝ | HurwitzStable B}
      {B | HurwitzUnstable B} := by
    rw [Set.disjoint_left]
    rintro B hs ⟨z,v,hz,hv⟩
    exact (not_lt_of_ge hz.le) (hs z v hv)
  have hcover : A '' S ⊆ {B | HurwitzStable B} ∪ {B | HurwitzUnstable B} := by
    rintro B ⟨t, ht, rfl⟩
    by_cases hs : HurwitzStable (A t)
    · exact Or.inl hs
    · right
      unfold HurwitzStable at hs
      push Not at hs
      obtain ⟨z,v,hv,hz⟩ := hs
      exact ⟨z,v,lt_of_le_of_ne hz (Ne.symm (haxis t ht z v hv)),hv⟩
  have hall := IsPreconnected.subset_left_of_subset_union isOpen_hurwitzStable
    isOpen_hurwitzUnstable hdis hcover ⟨A t₀, ⟨t₀, ht₀, rfl⟩, hbase⟩ himg
  intro t ht
  exact hall ⟨t, ht, rfl⟩

theorem hurwitzStable_path (A : ℝ → Matrix ι ι ℝ)
    (hA : ContinuousOn A (Set.Icc 0 1)) (hbase : HurwitzStable (A 0))
    (haxis : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ z v, HasEigenpair (A t) z v → z.re ≠ 0) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, HurwitzStable (A t) :=
  hurwitzStable_on_preconnected _ isPreconnected_Icc A hA haxis 0 (by simp) hbase

theorem isOpen_dUnstable : IsOpen {B : Matrix ι ι ℝ | DUnstable B} := by
  rw [isOpen_iff_mem_nhds]
  rintro B ⟨d, hd, hB⟩
  have hc : Continuous (fun C : Matrix ι ι ℝ => rightScale C d) := by
    unfold rightScale
    fun_prop
  have hn := (isOpen_hurwitzUnstable.preimage hc).mem_nhds hB
  filter_upwards [hn] with C hC
  exact ⟨d, hd, hC⟩

/-- The diagonal rate cone version used by hub and fixed-partition criteria. -/
theorem dStable_of_no_axis_of_one_scaling (B : Matrix ι ι ℝ)
    (d₀ : ι → ℝ) (hd₀ : ∀ i, 0 < d₀ i)
    (hbase : HurwitzStable (rightScale B d₀))
    (haxis : ∀ d : ι → ℝ, (∀ i, 0 < d i) →
      ∀ z v, HasEigenpair (rightScale B d) z v → z.re ≠ 0) : DStable B := by
  intro d hd
  let rates : ℝ → ι → ℝ := fun t i => (1-t)*d₀ i+t*d i
  let A : ℝ → Matrix ι ι ℝ := fun t => rightScale B (rates t)
  have hrates : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ i, 0 < rates t i := by
    intro t ht i
    dsimp [rates]
    have h₁ := mul_nonneg (sub_nonneg.mpr ht.2) (hd₀ i).le
    have h₂ := mul_nonneg ht.1 (hd i).le
    by_cases hzero : t=0
    · simp [hzero, hd₀ i]
    · have hp := mul_pos (lt_of_le_of_ne ht.1 (Ne.symm hzero)) (hd i)
      linarith
  have hc : Continuous A := by
    change Continuous (fun t : ℝ => fun i j => B i j * ((1-t)*d₀ j+t*d j))
    fun_prop
  have hzero : HurwitzStable (A 0) := by simpa [A, rates, rightScale] using hbase
  have ha : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ z v,
      HasEigenpair (A t) z v → z.re ≠ 0 := by
    intro t ht
    exact haxis (rates t) (hrates t ht)
  have hend := hurwitzStable_path A hc.continuousOn hzero ha 1 (by simp)
  simpa [A, rates, rightScale] using hend

end DStabilityCharacterization.SpectralContinuation

module

public import proofs.DUnstableCores.RouthHurwitzDim3

@[expose] public section

/-!
# Exact imaginary-pair boundary certificates

The complex eigenpair is exported as two real vectors.  These two coordinates
are the lossless interface needed by frequency-dependent separator messages.
-/

namespace DUnstableCores

def HasImaginaryPairWitness
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (omega : ℝ) (u v : ι → ℝ) : Prop :=
  0 < omega ∧ (u ≠ 0 ∨ v ≠ 0) ∧
    ∀ i, Matrix.mulVec A u i = -omega * v i ∧
      Matrix.mulVec A v i = omega * u i

theorem hasImaginaryPairWitness_of_hasEigenpair
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (omega : ℝ) (z : ι → ℂ)
    (homega : 0 < omega)
    (hz : HasEigenpair A ((omega : ℂ) * Complex.I) z) :
    HasImaginaryPairWitness A omega (fun i => (z i).re)
      (fun i => (z i).im) := by
  let u : ι → ℝ := fun i => (z i).re
  let v : ι → ℝ := fun i => (z i).im
  have huv : u ≠ 0 ∨ v ≠ 0 := by
    by_cases hu : u = 0
    · right
      intro hv
      apply hz.1
      funext i
      apply Complex.ext
      · have hi := congrFun hu i
        simpa [u] using hi
      · have hi := congrFun hv i
        simpa [v] using hi
    · exact Or.inl hu
  refine ⟨homega, huv, ?_⟩
  intro i
  have hi := hz.2 i
  have hre := congrArg Complex.re hi
  have him := congrArg Complex.im hi
  constructor
  · simpa [Matrix.mulVec, dotProduct, complexify, u, v,
      Complex.mul_re, Complex.mul_im] using hre
  · simpa [Matrix.mulVec, dotProduct, complexify, u, v,
      Complex.mul_re, Complex.mul_im] using him

structure SimpleImaginaryPairCertificate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) where
  omega : ℝ
  omega_pos : 0 < omega
  isRoot : (complexify A).charpoly.IsRoot ((omega : ℂ) * Complex.I)
  derivative_ne : (complexify A).charpoly.derivative.eval
    ((omega : ℂ) * Complex.I) ≠ 0

theorem SimpleImaginaryPairCertificate.sound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (C : SimpleImaginaryPairCertificate A) :
    ∃ u v : ι → ℝ,
      HasImaginaryPairWitness A C.omega u v ∧
      (complexify A).charpoly.derivative.eval
        ((C.omega : ℂ) * Complex.I) ≠ 0 := by
  obtain ⟨z, hz⟩ := hasEigenpair_of_isRoot_complexified_charpoly C.isRoot
  exact ⟨fun i => (z i).re, fun i => (z i).im,
    hasImaginaryPairWitness_of_hasEigenpair A C.omega z C.omega_pos hz,
    C.derivative_ne⟩

/-! ## Small exact phase/transversality model -/

def hopfCompanion4 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 0, -2;
     1, 0, 0, -3;
     0, 1, 0, -3;
     0, 0, 1, -3]

def hopfRight4 : Fin 4 → ℂ :=
  ![2 * Complex.I, 2 + 3 * Complex.I, 3 + Complex.I, 1]

def hopfLeft4 : Fin 4 → ℂ :=
  ![1, Complex.I, -1, -Complex.I]

def hopfPerturbation4 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, -1]

noncomputable def complexBilinearDot {ι : Type*} [Fintype ι]
    (x y : ι → ℂ) : ℂ := ∑ i, x i * y i

theorem hopfCompanion4_right_eigenpair :
    HasEigenpair hopfCompanion4 Complex.I hopfRight4 := by
  constructor
  · intro hzero
    have h3 := congrFun hzero 3
    simp [hopfRight4] at h3
  · intro i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, complexify, hopfCompanion4,
        hopfRight4, Fin.sum_univ_four]
    all_goals norm_num [Complex.ext_iff]

theorem hopfCompanion4_left_eigenpair :
    HasEigenpair hopfCompanion4.transpose Complex.I hopfLeft4 := by
  constructor
  · intro hzero
    have h0 := congrFun hzero 0
    simp [hopfLeft4] at h0
  · intro i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, complexify, hopfCompanion4,
        hopfLeft4, Matrix.transpose_apply, Fin.sum_univ_four]
    all_goals ring_nf

theorem hopfCompanion4_phase_pairing :
    complexBilinearDot hopfLeft4 hopfRight4 = -6 + 2 * Complex.I := by
  simp [complexBilinearDot, hopfLeft4, hopfRight4, Fin.sum_univ_four,
    mul_add]
  norm_num [Complex.ext_iff]

theorem hopfCompanion4_perturbation_pairing :
    complexBilinearDot hopfLeft4
      (Matrix.mulVec (complexify hopfPerturbation4) hopfRight4) =
        Complex.I := by
  simp [complexBilinearDot, Matrix.mulVec, dotProduct, complexify,
    hopfPerturbation4, hopfLeft4, hopfRight4, Fin.sum_univ_four]

theorem hopfCompanion4_crossing_derivative :
    complexBilinearDot hopfLeft4
        (Matrix.mulVec (complexify hopfPerturbation4) hopfRight4) /
      complexBilinearDot hopfLeft4 hopfRight4 =
        (1 : ℂ) / 20 - (3 : ℂ) / 20 * Complex.I := by
  rw [hopfCompanion4_phase_pairing, hopfCompanion4_perturbation_pairing]
  apply Complex.ext <;>
    norm_num [Complex.div_re, Complex.div_im, Complex.normSq_apply]

/-! ## Literal source realization and its forced D-unstable child -/

def hopfSource4 : SourceNetwork (Fin 4) (Fin 4) where
  reactant := !![1, 0, 0, 2;
                 0, 1, 0, 3;
                 0, 0, 1, 3;
                 0, 0, 0, 3]
  product := !![3, 2, 2, 0;
                4, 4, 3, 0;
                3, 4, 4, 0;
                3, 3, 4, 0]
  catalyst := 0
  catalyst_le_reactant := by intros; simp
  catalyst_le_product := by intros; simp

def hopfReactivity4 : Reactivity hopfSource4 where
  value := !![1, 0, 0, 0;
              0, 1, 0, 0;
              0, 0, 1, 0;
              1, 1, 1, 1]
  nonneg := by
    intro r s
    fin_cases r <;> fin_cases s <;> norm_num
  positive_of_reactant := by
    intro r s hrs
    fin_cases r <;> fin_cases s <;>
      simp [SourceNetwork.Reactant, hopfSource4] at hrs ⊢
  zero_of_not_reactant := by
    intro r s hrs
    fin_cases r <;> fin_cases s <;>
      simp [SourceNetwork.Reactant, hopfSource4] at hrs ⊢

theorem hopfSource4_jacobian :
    hopfSource4.jacobian hopfReactivity4 = hopfCompanion4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SourceNetwork.jacobian, SourceNetwork.stoich, hopfSource4,
      hopfReactivity4, hopfCompanion4, Fin.sum_univ_four] <;> norm_num

def hopfFullChild4 : ChildSelection hopfSource4 where
  species := Finset.univ
  reactions := Finset.univ
  assign := Equiv.refl _
  reactant_match := by
    intro x
    obtain ⟨i, hi⟩ := x
    fin_cases i <;>
      simp [hopfSource4, SourceNetwork.toReactionNetwork]

@[simp] theorem hopfFullChild4_assign_val (x : hopfFullChild4.species) :
    (hopfFullChild4.assign x).1 = x.1 := by
  rfl

noncomputable def hopfChildScale4 : hopfFullChild4.species → ℝ :=
  fun i => ![1 / 4, 1 / 7, 1 / 7, 1 / 7] i.1

def hopfChildVector4 : hopfFullChild4.species → ℝ :=
  fun i => ![4, 7, 7, 7] i.1

set_option maxHeartbeats 800000 in
theorem hopfFullChild4_dUnstable : DUnstable hopfFullChild4.realMatrix := by
  let cert : PositiveRealDInstabilityCertificate hopfFullChild4.realMatrix :=
    { scale := hopfChildScale4
      scale_pos := by
        intro i
        obtain ⟨i, hi⟩ := i
        fin_cases i <;> norm_num [hopfChildScale4]
      spectral :=
        { eigenvalue := 1
          eigenvector := hopfChildVector4
          eigenvalue_pos := by norm_num
          eigenvector_ne_zero := by
            intro hzero
            have h0 := congrFun hzero
              (⟨0, by simp [hopfFullChild4]⟩ : hopfFullChild4.species)
            norm_num [hopfChildVector4] at h0
          equation := by
            intro i
            obtain ⟨i, hi⟩ := i
            fin_cases i <;>
              norm_num [ChildSelection.realMatrix,
                AutocatalyticCS.ChildSelection.matrix,
                SourceNetwork.stoich, hopfFullChild4, hopfSource4,
                rightScale, hopfChildScale4, hopfChildVector4,
                Matrix.mulVec, dotProduct, Fin.sum_univ_four]
            all_goals simp [hopfFullChild4]
            all_goals rw [Fin.sum_univ_four]
            all_goals simp
            all_goals norm_num } }
  exact cert.sound

theorem hopfSource4_contains_DUnstableCore :
    ∃ core : ChildSelection hopfSource4, IsDUnstableCore core := by
  obtain ⟨core, _, hcore⟩ :=
    dUnstable_childSelection_contains_core hopfFullChild4 hopfFullChild4_dUnstable
  exact ⟨core, hcore⟩

end DUnstableCores

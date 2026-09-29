module

public import proofs.DUnstableCores.DScaling

@[expose] public section

/-!
# Exact spectral certificates

These structures are proof-carrying certificate formats.  A producer may use
floating-point arithmetic to discover a candidate, but acceptance requires the
exact real equalities and inequalities stored here.
-/

namespace DUnstableCores

variable {ι : Type*} [Fintype ι]

/-- Exact positive-real eigenpair certificate for a real matrix. -/
structure PositiveRealEigenpairCertificate (A : Matrix ι ι ℝ) where
  eigenvalue : ℝ
  eigenvector : ι → ℝ
  eigenvalue_pos : 0 < eigenvalue
  eigenvector_ne_zero : eigenvector ≠ 0
  equation : ∀ i, Matrix.mulVec A eigenvector i = eigenvalue * eigenvector i

theorem PositiveRealEigenpairCertificate.sound
    {A : Matrix ι ι ℝ} (c : PositiveRealEigenpairCertificate A) :
    HasPositiveRealEigenpair A := by
  exact ⟨c.eigenvalue, c.eigenvector, c.eigenvalue_pos,
    c.eigenvector_ne_zero, c.equation⟩

/-- A positive real eigenpair is, after scalar extension, a strict
right-half-plane complex eigenpair. -/
theorem hasPositiveRealEigenpair_implies_hurwitzUnstable
    {A : Matrix ι ι ℝ} (h : HasPositiveRealEigenpair A) :
    HurwitzUnstable A := by
  classical
  rcases h with ⟨lam, v, hlam, hv, heq⟩
  refine ⟨(lam : ℂ), (fun i => (v i : ℂ)), by simpa, ?_⟩
  constructor
  · intro hzero
    apply hv
    funext i
    have hi := congrFun hzero i
    exact Complex.ofReal_eq_zero.mp (by simpa using hi)
  · intro i
    have hi := congrArg (fun x : ℝ => (x : ℂ)) (heq i)
    simpa [Matrix.mulVec, dotProduct, complexify] using hi

theorem PositiveRealEigenpairCertificate.hurwitzUnstable
    {A : Matrix ι ι ℝ} (c : PositiveRealEigenpairCertificate A) :
    HurwitzUnstable A :=
  hasPositiveRealEigenpair_implies_hurwitzUnstable c.sound

/-- Exact D-instability witness: a positive right scaling together with a
positive-real eigenpair of the scaled matrix. -/
structure PositiveRealDInstabilityCertificate (A : Matrix ι ι ℝ) where
  scale : ι → ℝ
  scale_pos : ∀ i, 0 < scale i
  spectral : PositiveRealEigenpairCertificate (rightScale A scale)

theorem PositiveRealDInstabilityCertificate.sound
    {A : Matrix ι ι ℝ} (c : PositiveRealDInstabilityCertificate A) :
    DUnstable A := by
  exact ⟨c.scale, c.scale_pos, c.spectral.hurwitzUnstable⟩

end DUnstableCores

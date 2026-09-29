module

public import proofs.DUnstableCores.HopfFractionalMatching

@[expose] public section

/-!
# Exact quartic Hopf boundary invariant

For a monic real quartic, a nonzero imaginary root forces the two real
coefficient relations and annihilates the third Hurwitz determinant.  This is
the exact scalar whose source expansion must localize to a 2/3-child defect or
to a phase-carrying interaction circuit.
-/

namespace DUnstableCores

def quarticValue (a₁ a₂ a₃ a₄ : ℝ) (z : ℂ) : ℂ :=
  z ^ 4 + a₁ * z ^ 3 + a₂ * z ^ 2 + a₃ * z + a₄

def quarticDelta3 (a₁ a₂ a₃ a₄ : ℝ) : ℝ :=
  a₁ * a₂ * a₃ - a₃ ^ 2 - a₁ ^ 2 * a₄

theorem quartic_imaginary_root_relations
    (a₁ a₂ a₃ a₄ omega : ℝ) (homega : 0 < omega)
    (hroot : quarticValue a₁ a₂ a₃ a₄
      ((omega : ℂ) * Complex.I) = 0) :
    a₃ = a₁ * omega ^ 2 ∧
      a₄ = a₂ * omega ^ 2 - omega ^ 4 := by
  have him := congrArg Complex.im hroot
  have hre := congrArg Complex.re hroot
  simp [quarticValue, Complex.mul_re, Complex.mul_im, pow_succ] at him hre
  constructor <;> nlinarith

theorem quarticDelta3_eq_zero_of_imaginary_root
    (a₁ a₂ a₃ a₄ omega : ℝ) (homega : 0 < omega)
    (hroot : quarticValue a₁ a₂ a₃ a₄
      ((omega : ℂ) * Complex.I) = 0) :
    quarticDelta3 a₁ a₂ a₃ a₄ = 0 := by
  obtain ⟨h₃, h₄⟩ :=
    quartic_imaginary_root_relations a₁ a₂ a₃ a₄ omega homega hroot
  rw [h₃, h₄]
  simp [quarticDelta3]
  ring

end DUnstableCores

module

public import Mathlib
public import proofs.MAFComposition.Threshold

@[expose] public section

/-!
Source-faithful reaction factorization for the core-interaction calculus.

Reaction ownership is a function, hence every reaction occurs in exactly one
factor.  Supports retain every reactant, product, and explicit-catalyst
incidence.  Core labels are decorations and never participate in ownership.
-/

namespace CoreInteraction

variable {Species Reaction Factor CoreId : Type}
variable [Fintype Species] [Fintype Reaction] [Fintype Factor]
variable [DecidableEq Factor]

structure SourceNetwork (Species Reaction : Type) where
  input : Matrix Species Reaction ℝ
  output : Matrix Species Reaction ℝ
  catalyst : Matrix Species Reaction ℝ

def SourceNetwork.toMAFNetwork (Q : SourceNetwork Species Reaction) :
    MAFComposition.Network Species Reaction where
  input := Q.input
  output := Q.output

structure Factorization (Q : SourceNetwork Species Reaction)
    (Factor CoreId : Type) where
  owner : Reaction → Factor
  support : Factor → Species → Prop
  support_decidable : ∀ f s, Decidable (support f s)
  support_complete : ∀ f s r, owner r = f →
    Q.input s r ≠ 0 ∨ Q.output s r ≠ 0 ∨ Q.catalyst s r ≠ 0 → support f s
  coreDecorations : Factor → Finset CoreId

attribute [instance] Factorization.support_decidable

namespace Factorization

variable {Q : SourceNetwork Species Reaction}

def factorInput (fac : Factorization Q Factor CoreId) (f : Factor) :
    Matrix Species Reaction ℝ :=
  fun s r => if fac.owner r = f then Q.input s r else 0

def factorOutput (fac : Factorization Q Factor CoreId) (f : Factor) :
    Matrix Species Reaction ℝ :=
  fun s r => if fac.owner r = f then Q.output s r else 0

def factorCatalyst (fac : Factorization Q Factor CoreId) (f : Factor) :
    Matrix Species Reaction ℝ :=
  fun s r => if fac.owner r = f then Q.catalyst s r else 0

omit [Fintype Species] [Fintype Reaction] in
@[simp] theorem sum_factorInput (fac : Factorization Q Factor CoreId)
    (s : Species) (r : Reaction) :
    ∑ f : Factor, fac.factorInput f s r = Q.input s r := by
  simp [factorInput]

omit [Fintype Species] [Fintype Reaction] in
@[simp] theorem sum_factorOutput (fac : Factorization Q Factor CoreId)
    (s : Species) (r : Reaction) :
    ∑ f : Factor, fac.factorOutput f s r = Q.output s r := by
  simp [factorOutput]

omit [Fintype Species] [Fintype Reaction] in
@[simp] theorem sum_factorCatalyst (fac : Factorization Q Factor CoreId)
    (s : Species) (r : Reaction) :
    ∑ f : Factor, fac.factorCatalyst f s r = Q.catalyst s r := by
  simp [factorCatalyst]

omit [Fintype Species] [Fintype Reaction] [Fintype Factor] [DecidableEq Factor] in
theorem owned_support (fac : Factorization Q Factor CoreId)
    {f : Factor} {s : Species} {r : Reaction} (hown : fac.owner r = f)
    (hsource : Q.input s r ≠ 0 ∨ Q.output s r ≠ 0 ∨ Q.catalyst s r ≠ 0) :
    fac.support f s :=
  fac.support_complete f s r hown hsource

/-- The factor residual uses the literal source columns owned by the factor. -/
def residual (fac : Factorization Q Factor CoreId) (q : ℝ)
    (x : Reaction → ℝ) (f : Factor) (s : Species) : ℝ :=
  ∑ r : Reaction, if fac.owner r = f then
    (Q.output s r - q * Q.input s r) * x r else 0

def globalResidual (Q : SourceNetwork Species Reaction) (q : ℝ)
    (x : Reaction → ℝ) (s : Species) : ℝ :=
  ∑ r : Reaction, (Q.output s r - q * Q.input s r) * x r

omit [Fintype Species] [Fintype Factor] in
theorem residual_eq_zero_of_not_support (fac : Factorization Q Factor CoreId)
    (q : ℝ) (x : Reaction → ℝ) {f : Factor} {s : Species}
    (hnot : ¬ fac.support f s) : fac.residual q x f s = 0 := by
  apply Finset.sum_eq_zero
  intro r _
  by_cases hown : fac.owner r = f
  · have hin : Q.input s r = 0 := by
      by_contra hne
      exact hnot (fac.support_complete f s r hown (Or.inl hne))
    have hout : Q.output s r = 0 := by
      by_contra hne
      exact hnot (fac.support_complete f s r hown (Or.inr (Or.inl hne)))
    simp [hown, hin, hout]
  · simp [hown]

omit [Fintype Species] in
/-- `MAF-RESIDUAL-SPLIT`: ownership makes the global residual the exact sum
of local residuals, with no duplicated or omitted reaction contribution. -/
theorem residual_sum_eq_global (fac : Factorization Q Factor CoreId)
    (q : ℝ) (x : Reaction → ℝ) (s : Species) :
    ∑ f : Factor, fac.residual q x f s = globalResidual Q q x s := by
  rw [globalResidual]
  simp_rw [residual]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  simp

omit [Fintype Species] [Fintype Factor] [DecidableEq Factor] in
theorem toMAFNetwork_netMatrix_mulVec
    (q : ℝ) (x : Reaction → ℝ) (s : Species) :
    (Q.toMAFNetwork.netMatrix q).mulVec x s = globalResidual Q q x s := by
  rfl

end Factorization

end CoreInteraction

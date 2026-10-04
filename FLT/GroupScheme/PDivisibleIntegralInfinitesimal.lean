/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleIntegralTangentCoefficients
public import FLT.GroupScheme.PDivisibleNilpotentCotangent

/-! # The original integral tangent represents actual infinitesimal points -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K B C : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
  (X : PDivisibleSystem R K p height)

/-- The integral tangent with coefficients in the actual reduction kernel represents
the original infinitesimal point functor; freeness is proved internally. -/
def integralTangentInfinitesimalEquiv (e : R ≃+* ℤ_[p])
    (q : B →ₐ[R] C) (hJ : RingHom.ker q ^ 2 = ⊥) (hB : IsNilpotent (p : B)) :
    X.IntegralTangent ⊗[R] RingHom.ker q ≃ X.InfinitesimalColimit q := by
  let (n : ℕ) : Finite (X.LevelCotangent n) := X.levelCotangent_finite_of_equiv e n
  exact (X.integralTangentCoefficientsEquiv e).toEquiv.trans
    (X.nilpotentInfinitesimalCotangentEquiv q hJ hB).symm

/-- The represented infinitesimal point retains the original integral evaluation pairing. -/
theorem integralTangentInfinitesimalEquiv_pairing (e : R ≃+* ℤ_[p])
    (q : B →ₐ[R] C) (hJ : RingHom.ker q ^ 2 = ⊥) (hB : IsNilpotent (p : B))
    (d : X.IntegralTangent) (a : RingHom.ker q) (n : ℕ)
    (f : X.LevelInfinitesimalKernel q n)
    (hf : X.integralTangentInfinitesimalEquiv e q hJ hB (d ⊗ₜ a) =
      X.infinitesimalColimitMk q n f) (x : X.cotangentLimit) :
    X.infinitesimalLimitPairing q hJ n f x = X.integralTangentPairing d x • a := by
  let (n : ℕ) : Finite (X.LevelCotangent n) := X.levelCotangent_finite_of_equiv e n
  have he := congrArg (X.nilpotentInfinitesimalCotangentEquiv q hJ hB) hf
  rw [X.nilpotentInfinitesimalCotangentEquiv_mk] at he
  change (X.nilpotentInfinitesimalCotangentEquiv q hJ hB)
    ((X.nilpotentInfinitesimalCotangentEquiv q hJ hB).symm
      (X.integralTangentCoefficientsEquiv e (d ⊗ₜ a))) = _ at he
  rw [Equiv.apply_symm_apply] at he
  exact (LinearMap.congr_fun he x).symm

end ThreeAdicPlan.PDivisibleSystem

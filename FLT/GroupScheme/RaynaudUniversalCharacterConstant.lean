/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudScalarConvolution

/-!
# Universal iterated character constants

Extend characters by zero at the origin and apply the iterated reduced
average. The result involves only the finite field and its characters.
On any integral character vector, convolution powers act by this scalar.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open WithConv
namespace CharacterAverage

variable {R F : Type*} [CommRing R] [Field F]

/-- A multiplicative character extended by zero, including the trivial character. -/
def value (χ : Fˣ →* Rˣ) (a : F) : R := by
  classical
  exact if h : a = 0 then 0 else χ (Units.mk0 a h)

/-- The extended character vanishes at the origin. -/
@[simp] theorem value_zero (χ : Fˣ →* Rˣ) : value χ 0 = 0 := by simp [value]

/-- On scalar units the extension is the original character. -/
@[simp] theorem value_unit (χ : Fˣ →* Rˣ) (u : Fˣ) : value χ u = (χ u : R) := by
  simp [value, Units.ne_zero u]

variable [Fintype Fˣ] [Invertible (Fintype.card Fˣ : R)]

/-- The universal n-fold constant, with prescribed input and output characters. -/
def constant (χ ψ : Fˣ →* Rˣ) (n : ℕ) : R := iterate χ (value ψ) n 0

end CharacterAverage

variable {R K F : Type} [CommRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] [Field F] [Fintype Fˣ]
  [Invertible (Fintype.card Fˣ : R)] (X : FF R K)
  (lift : F → ModelHom X X) (h0 : lift 0 = ModelHom.zero X X)
  (h1 : lift 1 = BialgHom.id R X.CoordinateRing)
  (hmul : ∀ a b, lift (a * b) = (lift b).comp (lift a))
  (hadd : ∀ a b, lift (a + b) = (lift a).add (lift b))

include h0 in
omit [PerfectField K] [IsFractionRing R K] [Invertible (Fintype.card Fˣ : R)]
  [Fintype Fˣ] in
/-- All scalars, including zero, act by the extended character on augmentation vectors. -/
theorem FF.integralCharacter_scalar_value (ψ : Fˣ →* Rˣ)
    (v : X.integralCharacter lift h1 hmul ψ) (a : F) :
    lift a (v.val : X.CoordinateRing) =
      CharacterAverage.value ψ a • (v.val : X.CoordinateRing) := by
  by_cases ha : a = 0
  · subst a
    rw [h0, CharacterAverage.value_zero, zero_smul]
    change algebraMap R X.CoordinateRing (Coalgebra.counit (v.val : X.CoordinateRing)) = 0
    rw [v.val.property, map_zero]
  · simpa only [CharacterAverage.value, dite_eq_right ha, Units.val_mk0] using
      X.integralCharacter_scalar lift h1 hmul ψ v (Units.mk0 a ha)

include h0 hadd in
/-- The convolution power on a character vector is the universal scalar times that vector. -/
theorem FF.characterProjector_convPow_eigen (χ ψ : Fˣ →* Rˣ) (n : ℕ)
    (v : X.integralCharacter lift h1 hmul ψ) :
    (toConv (X.coordinateCharacterProjector lift h1 hmul χ) ^ n) (v.val : X.CoordinateRing) =
      CharacterAverage.constant χ ψ n • (v.val : X.CoordinateRing) := by
  let ev : WithConv (X.CoordinateRing →ₗ[R] X.CoordinateRing) →ₗ[R] X.CoordinateRing :=
    { toFun := fun f ↦ f (v.val : X.CoordinateRing)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  change ev _ = _
  rw [X.characterProjector_convPow lift h0 h1 hmul hadd, CharacterAverage.map_iterate]
  change CharacterAverage.iterate χ (fun a ↦ lift a (v.val : X.CoordinateRing)) n 0 = _
  simp_rw [X.integralCharacter_scalar_value lift h0 h1 hmul ψ v]
  exact (CharacterAverage.map_iterate χ (CharacterAverage.value ψ)
    (LinearMap.toSpanSingleton R X.CoordinateRing (v.val : X.CoordinateRing)) n 0).symm

end ThreeAdicPlan

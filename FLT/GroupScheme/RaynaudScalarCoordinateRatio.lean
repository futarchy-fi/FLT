/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudEvaluatedCycle

/-!
# Scalar automorphisms and actual coordinate ratios

The actual coordinate ratio is the lifted scalar character. No root equation
or inertia-character identification is assumed in this calculation.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open IsLocalRing

variable {R L F : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [HenselianLocalRing R] [IsSepClosed (ResidueField R)] [Field L] [Algebra R L]
  [CharZero L] [IsFractionRing R L] [Field F] [Fintype F] [DecidableEq F]
  (X : FF R L) [Module F X.Points]
  (lift : F → ModelHom X X) (h1 : lift 1 = BialgHom.id R X.CoordinateRing)
  (hmul : ∀ a b, lift (a * b) = (lift b).comp (lift a))
  (p : ℕ) [CharP F p] [CharP (ResidueField R) p]
  (hdim : Module.finrank F X.Points = 1)
  (hlift : ∀ a x, genericHom (lift a) x = a • x) (ε : F →+* ResidueField R)

/-- Actual fundamental values transform by the lifted scalar character. -/
theorem FF.fundamentalValue_scalar (i : ℕ) (u : Fˣ) (x : X.Points) :
    X.fundamentalValue lift h1 hmul p hdim hlift ε i ((u : F) • x) =
      algebraMap R (AlgebraicClosure L) ((fundamentalCharacter p ε u : R) ^ (p ^ i)) *
        X.fundamentalValue lift h1 hmul p hdim hlift ε i x := by
  simpa only [FF.fundamentalValue, FF.fundamentalCoordinate, FF.characterGenerator,
    MonoidHom.pow_apply, Units.val_pow_eq_pow_val] using
    X.integralCharacter_eval_scalar lift h1 hmul hlift
      (fundamentalCharacter p ε ^ (p ^ i))
      (X.characterBasis lift h1 hmul p hdim hlift _ ()) u x

/-- A scalar point action determines the actual coordinate ratio. -/
theorem FF.fundamentalValue_ratio (i : ℕ) (u : Fˣ) (x : X.Points) (hx : x ≠ 0)
    (σ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L)
    (hσ : σ • x = (u : F) • x) :
    σ (X.fundamentalValue lift h1 hmul p hdim hlift ε i x) /
        X.fundamentalValue lift h1 hmul p hdim hlift ε i x =
      algebraMap R (AlgebraicClosure L) ((fundamentalCharacter p ε u : R) ^ (p ^ i)) := by
  have h := (X.characterCoordinates
    (X.fundamentalCoordinate p lift h1 hmul hdim hlift ε i)).map_smul σ x
  change X.fundamentalValue lift h1 hmul p hdim hlift ε i (σ • x) =
    σ (X.fundamentalValue lift h1 hmul p hdim hlift ε i x) at h
  rw [← h, hσ, X.fundamentalValue_scalar lift h1 hmul p hdim hlift ε]
  exact mul_div_cancel_right₀ _ (X.fundamentalCoordinate_eval_ne_zero
    lift h1 hmul hlift p hdim ε i x hx)

end ThreeAdicPlan

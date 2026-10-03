/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudActualCyclicPresentation
public import FLT.GroupScheme.RaynaudPointCoordinate
public import FLT.GroupScheme.RaynaudTwoCoordinates

/-!
# Root equations obtained from actual Raynaud coordinates

Evaluate the constructed cyclic relations on an actual nonzero generic point,
then eliminate one or two coordinates. This uses no supplied point equations.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open IsLocalRing

variable {R K F : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [HenselianLocalRing R] [IsSepClosed (ResidueField R)] [Field K] [Algebra R K]
  [CharZero K] [IsFractionRing R K] [Field F] [Fintype F] [DecidableEq F]
  (X : FF R K) [Module F X.Points]
  (lift : F → ModelHom X X) (h1 : lift 1 = BialgHom.id R X.CoordinateRing)
  (hmul : ∀ a b, lift (a * b) = (lift b).comp (lift a))
  (p : ℕ) [CharP F p] [CharP (ResidueField R) p]
  (hdim : Module.finrank F X.Points = 1)
  (hlift : ∀ a x, genericHom (lift a) x = a • x) (e : F →+* ResidueField R)

/-- Evaluate a fundamental coordinate on an actual generic point. -/
def FF.fundamentalValue (i : ℕ) (x : X.Points) : AlgebraicClosure K :=
  X.characterCoordinates (X.fundamentalCoordinate p lift h1 hmul hdim hlift e i) x

/-- Evaluation preserves the actual cyclic power equation. -/
theorem FF.fundamentalValue_power (r : ℕ+) (hr : Fintype.card F = p ^ (r : ℕ))
    (i : Fin r) (x : X.Points) :
    X.fundamentalValue lift h1 hmul p hdim hlift e i x ^ p =
      algebraMap R (AlgebraicClosure K)
        (X.fundamentalCoefficient lift h1 hmul p hdim hlift e r hr i) *
      X.fundamentalValue lift h1 hmul p hdim hlift e (cycleNext r i) x := by
  have h := congrArg (fun c : X.CoordinateRing ↦ X.characterCoordinates c)
    (X.fundamentalCoefficient_spec lift h1 hmul p hdim hlift e r hr i)
  rw [map_pow, map_smul] at h
  have he := congrArg (MulActionHom.evalAlgHom _ R X.Points (AlgebraicClosure K) x) h
  rw [map_pow, map_smul, Algebra.smul_def] at he
  exact he

/-- The one-coordinate root equation uses the coefficient of the actual presentation. -/
theorem FF.fundamentalValue_one (hr : Fintype.card F = p ^ (1 : ℕ))
    (x : X.Points) (hx : x ≠ 0) :
    X.fundamentalValue lift h1 hmul p hdim hlift e 0 x ^ (p - 1) =
      algebraMap R (AlgebraicClosure K)
        (X.fundamentalCoefficient lift h1 hmul p hdim hlift e 1 hr 0) := by
  apply RaynaudParameters.coordinate_one (CharP.char_is_prime F p).one_lt.le
    (X.fundamentalCoordinate_eval_ne_zero lift h1 hmul hlift p hdim e 0 x hx)
  simpa [cycleNext, FF.fundamentalValue] using
    X.fundamentalValue_power lift h1 hmul p hdim hlift e 1 hr 0 x

/-- Elimination of the actual two-cycle gives the Frobenius-weighted coefficient product. -/
theorem FF.fundamentalValue_two (hr : Fintype.card F = p ^ (2 : ℕ))
    (x : X.Points) (hx : x ≠ 0) :
    X.fundamentalValue lift h1 hmul p hdim hlift e 0 x ^ (p * p - 1) =
      algebraMap R (AlgebraicClosure K)
        ((X.fundamentalCoefficient lift h1 hmul p hdim hlift e 2 hr 0) ^ p *
          X.fundamentalCoefficient lift h1 hmul p hdim hlift e 2 hr 1) := by
  rw [map_mul, map_pow]
  apply RaynaudParameters.coordinate_two (CharP.char_is_prime F p).one_lt.le
    (X.fundamentalCoordinate_eval_ne_zero lift h1 hmul hlift p hdim e 0 x hx)
  · simpa [cycleNext, FF.fundamentalValue] using
      X.fundamentalValue_power lift h1 hmul p hdim hlift e 2 hr 0 x
  · simpa [cycleNext, FF.fundamentalValue] using
      X.fundamentalValue_power lift h1 hmul p hdim hlift e 2 hr 1 x

end ThreeAdicPlan

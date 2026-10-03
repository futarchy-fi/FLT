/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCoordinateScalings
public import FLT.GroupScheme.RaynaudFundamentalCycleParameters
public import FLT.GroupScheme.RaynaudScalingUnits

/-!
# Unit scalings on the actual fundamental cycle

The scalings come from coordinate pullback on the derived bases. The
cyclic parameter products and power equations are all proved for those
same bases, so the small-ramification valuation argument applies directly.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open IsLocalRing

variable {R K F : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [IsSepClosed (ResidueField R)] [Field K] [Algebra R K]
  [CharZero K] [IsFractionRing R K] [Field F] [Fintype F] [DecidableEq F]
  [Invertible (Fintype.card Fˣ : R)] {X Y : FF R K}
  [Module F X.Points] [Module F Y.Points] (f : ModelHom X Y)
  (sx : F → ModelHom X X) (sy : F → ModelHom Y Y)
  (hx0 : sx 0 = ModelHom.zero X X) (hy0 : sy 0 = ModelHom.zero Y Y)
  (hx1 : sx 1 = BialgHom.id R X.CoordinateRing)
  (hy1 : sy 1 = BialgHom.id R Y.CoordinateRing)
  (hxm : ∀ a b, sx (a * b) = (sx b).comp (sx a))
  (hym : ∀ a b, sy (a * b) = (sy b).comp (sy a))
  (hxa : ∀ a b, sx (a + b) = (sx a).add (sx b))
  (hya : ∀ a b, sy (a + b) = (sy a).add (sy b))
  (hcomm : ∀ a, f.comp (sy a) = (sx a).comp f)
  (p : ℕ) [CharP F p] [CharP (ResidueField R) p]
  (hdx : Module.finrank F X.Points = 1) (hdy : Module.finrank F Y.Points = 1)
  (hsx : ∀ a x, genericHom (sx a) x = a • x)
  (hsy : ∀ a y, genericHom (sy a) y = a • y)
  (e : F →+* ResidueField R) (r : ℕ+) (hr : Fintype.card F = p ^ (r : ℕ))

include hx0 hy0 hxa hya hr in
/-- All derived fundamental scalings of a generic isomorphism are units below e<p−1. -/
theorem ModelHom.isUnit_fundamental_scaling (hf : Function.Surjective (genericHom f))
    (he : RaynaudParameters.order (p : R) < p - 1) (i : Fin r) :
    IsUnit (f.characterScaling sx sy hx1 hy1 hxm hym hcomm p hdx hdy hsx hsy
      (fundamentalCharacter p e ^ (p ^ i.val))) := by
  let χ : Fin r → (Fˣ →* Rˣ) := fun j ↦ fundamentalCharacter p e ^ (p ^ j.val)
  let c := fun j ↦ f.characterScaling sx sy hx1 hy1 hxm hym hcomm p hdx hdy hsx hsy (χ j)
  let ax := X.fundamentalCoefficient sx hx1 hxm p hdx hsx e r hr
  let ay := Y.fundamentalCoefficient sy hy1 hym p hdy hsy e r hr
  have hp : p.Prime := CharP.char_is_prime F p
  have hpR : (p : R) ≠ 0 := by
    intro hz
    have hz' := congrArg (algebraMap R K) hz
    exact (Nat.cast_ne_zero.mpr hp.ne_zero : (p : K) ≠ 0) (by simpa using hz')
  apply RaynaudParameters.isUnit_cyclic_scalings p hp.one_le hpR he (cycleNext r) ax ay c
    (X.fundamentalCoefficient_complement sx hx0 hx1 hxm hxa p hdx hsx e r hr)
    (Y.fundamentalCoefficient_complement sy hy0 hy1 hym hya p hdy hsy e r hr)
    (fun j ↦ f.characterScaling_ne_zero sx sy hx1 hy1 hxm hym hcomm p hdx hdy hsx hsy hf (χ j))
    _ i
  intro j
  have hpow : χ j ^ p = χ (cycleNext r j) := fundamentalCharacter_cycle_pow p e r hr j
  have hx : X.characterGenerator sx hx1 hxm p hdx hsx (χ j) ^ p =
      ax j • X.characterGenerator sx hx1 hxm p hdx hsx (χ j ^ p) := by
    rw [hpow]
    exact X.fundamentalCoefficient_spec sx hx1 hxm p hdx hsx e r hr j
  have hy : Y.characterGenerator sy hy1 hym p hdy hsy (χ j) ^ p =
      ay j • Y.characterGenerator sy hy1 hym p hdy hsy (χ j ^ p) := by
    rw [hpow]
    exact Y.fundamentalCoefficient_spec sy hy1 hym p hdy hsy e r hr j
  simpa only [hpow] using
    f.characterScaling_power sx sy hx1 hy1 hxm hym hcomm p hdx hdy hsx hsy (χ j) p
      (ax j) (ay j) hx hy

end ThreeAdicPlan

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRetainedNodeFactorRatioMap

/-!
# Reduction of the full retained correction

The original opposite factor reduces to a1. Its square tangent correction
therefore reduces to one under every map killing the coefficient ideal.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassModificationX
open PolygonSmoothing
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (π s c3 c4 c6 : R)
  (I : Ideal R) (hI : IsNilpotent I) (ha : IsUnit W.a₁)
  (hs : s ∈ I) (h2 : W.a₂ ∈ I) (h3 : c3 ∈ I) (h4 : c4 ∈ I) (h6 : c6 ∈ I)
local notation "B" => ChartRing (R := R) π
local notation "J" => I.map (algebraMap R B)
local notation "V" => retainedFactorCorrectionUnit W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6
local notation "U" => retainedOppositeUnit W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6
local notation "a" => zeroInitialTangentUnit W ha

attribute [local irreducible] retainedOppositeFactor retainedOppositeUnit
  retainedFactorCorrectionUnit retainedSlopeRoot retainedConicRoot

/-- The whole opposite factor differs from the original tangent by the coefficient ideal. -/
theorem retainedOppositeFactor_sub_tangent_mem :
    retainedOppositeFactor W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6 -
      algebraMap R B W.a₁ ∈ J := by
  have h := (J).add_mem ((J).add_mem
    (retainedSlopeRoot_mem W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6)
    (retainedConicRoot_mem W π c3 c4 c6 I hI ha h2 h3 h4 h6))
    ((J).mul_mem_right (leftCoordinate π) (Ideal.mem_map_of_mem _ h3))
  convert h using 1
  unfold retainedOppositeFactor retainedSlopeLinear
  ring

variable {S : Type*} [CommRing S] (f : ChartRing π →+* S)
  (hf : I.map (algebraMap R (ChartRing π)) ≤ RingHom.ker f)
include hf

/-- Every reduction killing the coefficient ideal sends the full factor to the tangent. -/
theorem retainedOppositeFactor_reduction :
    f (retainedOppositeFactor W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6) =
      f (algebraMap R B W.a₁) := by
  have h := hf (retainedOppositeFactor_sub_tangent_mem W π s c3 c4 c6
    I hI ha hs h2 h3 h4 h6)
  change f (_ - _) = 0 at h
  exact sub_eq_zero.mp ((map_sub f _ _).symm.trans h)

/-- The full opposite unit reduces to the original coefficient unit. -/
theorem retainedOppositeUnit_reduction :
    Units.map f.toMonoidHom U =
      Units.map (f.comp (algebraMap R B)).toMonoidHom a := by
  apply Units.ext
  change f (U : B) = f (algebraMap R B (a : R))
  rw [retainedOppositeUnit_val]
  exact retainedOppositeFactor_reduction W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6 f hf

/-- No residual root correction survives: the entire squared correction reduces to one. -/
theorem retainedFactorCorrectionUnit_reduction : Units.map f.toMonoidHom V = 1 := by
  rw [retainedFactorCorrectionUnit, map_mul, map_pow, map_pow, map_inv,
    retainedOppositeUnit_reduction W π s c3 c4 c6 I hI ha hs h2 h3 h4 h6 f hf]
  change (Units.map (f.comp (algebraMap R B)).toMonoidHom a) ^ 2 *
    (Units.map (f.comp (algebraMap R B)).toMonoidHom a)⁻¹ ^ 2 = 1
  rw [← mul_pow, mul_inv_cancel, one_pow]

end FLT.Mazur.WeierstrassModificationX

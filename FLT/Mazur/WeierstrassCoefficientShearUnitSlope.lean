/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearScaleOneParameter

/-!
# The original tensor slope comparison with a chosen unit tangent difference

Transport along the coefficient equality retains all original cubic
coordinates and the complete Laurent map, rather than only the unit value.
-/

@[expose] public noncomputable section
open scoped TensorProduct LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
open WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Equality of tangent coefficients identifies the full slope localization. -/
def slopeCoefficientCongr {S : Type*} [CommRing S] (b c : S) (h : b = c) :
    SlopeOpen b ≃ₐ[S] SlopeOpen c := h ▸ AlgEquiv.refl

/-- The coefficient identification preserves the original slope function. -/
theorem slopeCoefficientCongr_z {S : Type*} [CommRing S] (b c : S) (h : b = c) :
    slopeCoefficientCongr b c h (slopeZ b) = slopeZ c := by subst c; rfl

/-- Transport and its inverse preserve the whole Laurent algebra map. -/
theorem slopeCoefficientCongr_laurent {S : Type*} [CommRing S] (a : Sˣ)
    (b : S) (h : (a : S) = b) :
    (slopeCoefficientCongr b (a : S) h.symm).toAlgHom.comp (h ▸ slopeLaurentMap a) =
      slopeLaurentMap a := by subst b; rfl

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (S : Type*) [CommRing S] [Algebra R S] (r : S)
  (hs : algebraMap R S s = 1) (h3 : algebraMap R S b3 = 0)
  (h4 : algebraMap R S b4 = 0) (h6 : algebraMap R S b6 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "T" => ScalarExtension W s b3 b4 b6 S
local notation "P" => SlopeOpen (a : S)
local notation "z" => slopeZ (a : S)
local notation "E" => tensorShearScaleOneEquiv W s b3 b4 b6 S r hs h3 h4 h6 hr

/-- The full original tensor comparison indexed by the chosen unit tangent difference. -/
def tensorShearUnitSlopeEquiv : T ≃ₐ[S] P :=
  (E).trans (slopeCoefficientCongr _ (a : S) ha.symm)

local notation "F" => tensorShearUnitSlopeEquiv W s b3 b4 b6 S r hs h3 h4 h6 hr a ha

/-- The original horizontal tensor remains the product of the two tangent functions. -/
theorem tensorShearUnitSlopeEquiv_x :
    F ((1 : S) ⊗ₜ[R] x W s b3 b4 b6) = z * (z + algebraMap S P (a : S)) := by
  rw [tensorShearUnitSlopeEquiv, AlgEquiv.trans_apply, tensorShearScaleOneEquiv_x,
    map_mul, map_add, AlgEquiv.commutes, slopeCoefficientCongr_z, ← ha]

/-- The original vertical tensor keeps its actual root shift. -/
theorem tensorShearUnitSlopeEquiv_y :
    F ((1 : S) ⊗ₜ[R] y W s b3 b4 b6) =
      z * (z + algebraMap S P (a : S)) * (z + algebraMap S P r) := by
  rw [tensorShearUnitSlopeEquiv, AlgEquiv.trans_apply, tensorShearScaleOneEquiv_y,
    map_mul, map_mul, map_add, map_add, AlgEquiv.commutes, AlgEquiv.commutes,
    slopeCoefficientCongr_z, ← ha]

/-- Every Laurent function commutes with the full unit-indexed tensor comparison. -/
theorem tensorShearUnitSlopeEquiv_laurent :
    (F).toAlgHom.comp (tensorShearScaleOneLaurentMap W s b3 b4 b6 S r hs h3 h4 h6 hr) =
      slopeLaurentMap a := by
  change (slopeCoefficientCongr _ (a : S) ha.symm).toAlgHom.comp
    ((E).toAlgHom.comp
      (tensorShearScaleOneLaurentMap W s b3 b4 b6 S r hs h3 h4 h6 hr)) = _
  rw [tensorShearScaleOneLaurentMap_comparison W s b3 b4 b6 S r hs h3 h4 h6 hr a ha,
    slopeCoefficientCongr_laurent]

end FLT.Mazur.WeierstrassModificationX

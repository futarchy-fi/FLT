/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGenericClosureSmoothDensity
public import FLT.Mazur.WeierstrassSmoothGoodReductionGroup
public import FLT.Mazur.WeierstrassSmoothCoefficientGroupIso

/-!
# The original generic group and the integral smooth group

Good generic reduction identifies the original generic cubic group with the
base change of the integral smooth group. The projection is the previously
constructed smooth factorization of the original coefficient morphism.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassDividedDepth

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  (W : WeierstrassCurve R) (hΔ : IsUnit (W.map (algebraMap R K)).Δ)

local notation "V" => W.map (algebraMap R K)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))

/-- The exact generic cubic group is the base change of the original integral smooth group. -/
def genericSmoothGroupIso :
    integralCurveGroup V hΔ ≅ originalSmoothBaseChangeGroup K W :=
  (integralSmoothGoodReductionGroupIso V hΔ).symm ≪≫
    originalSmoothCoefficientGroupIso K W

/-- Its original geometric projection is the retained smooth coefficient factorization. -/
@[reassoc] theorem genericSmoothGroupIso_fst :
    (genericSmoothGroupIso W hΔ).hom.hom.hom.hom.left ≫
      pullback.fst (integralSmoothStructure W) q = genericCurveToIntegralSmooth W hΔ := by
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  rw [Category.assoc, genericCurveToIntegralSmooth_inclusion]
  change ((integralSmoothGoodReductionGroupIso V hΔ).inv.hom.hom.hom.left ≫
    (originalSmoothCoefficientIso K W).hom) ≫ _ = _
  rw [Category.assoc, originalSmoothCoefficientIso_fst_assoc,
    originalSmoothCoefficientMap_inclusion, ← Category.assoc]
  have hi : (integralSmoothGoodReductionGroupIso V hΔ).inv.hom.hom.hom.left ≫
      (integralSmoothOpen V).ι = 𝟙 _ :=
    congrArg (fun f => f.hom.hom.hom.left)
      (Iso.inv_hom_id (integralSmoothGoodReductionGroupIso V hΔ))
  rw [hi, Category.id_comp]

/-- The original generic curve's smooth factorization retains its coefficient structure. -/
@[reassoc] theorem genericCurveToIntegralSmooth_structure :
    genericCurveToIntegralSmooth W hΔ ≫ integralSmoothStructure W =
      integralCurveStructure V ≫ q := by
  rw [integralSmoothStructure, ← Category.assoc, genericCurveToIntegralSmooth_inclusion]
  exact integralCoefficientMorphism_structure W

end FLT.Mazur.WeierstrassIntegralChart

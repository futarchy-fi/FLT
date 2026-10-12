/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassCartesianOriginComparison

/-!
# A chosen pointed cartesian cubic realizes the actual pullback group

Compose the proved coefficient group comparison with the pointed comparison.
Its inverse projects to exactly the specified original cartesian morphism.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (V : WeierstrassCurve S)
  (f : integralCurve V ⟶ integralCurve W)
  (hf : IsPullback f (integralCurveStructure V) (integralCurveStructure W)
    (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  (hz : integralCurveZero V ≫ f =
    Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ integralCurveZero W)
  (hW : IsUnit W.Δ) (hV : IsUnit V.Δ)
local notation "U" => W.map (algebraMap R S)
local notation "F" => Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))

/-- The independently chosen cartesian cubic realizes the actual monoidal pullback group. -/
irreducible_def cartesianPullbackGroupIso :
    (F).mapCommGrp.obj (integralCurveGroup W hW) ≅ integralCurveGroup V hV := by
  have hU : IsUnit (U).Δ := by
    rw [WeierstrassCurve.map_Δ]
    exact hW.map (algebraMap R S)
  exact (integralCurveCoefficientGroupIso W hW hU).symm ≪≫
    cartesianCoefficientGroupIso W V f hf hz hU hV

/-- The forward map retains the original two cartesian comparisons. -/
theorem cartesianPullbackGroupIso_hom :
    (cartesianPullbackGroupIso W V f hf hz hW hV).hom.hom.hom.hom.left =
      (integralCurveCoefficientBaseChangeIso W).inv ≫
        (cartesianCoefficientIso W V f hf).hom := by
  rw [cartesianPullbackGroupIso_def]
  change (integralCurveCoefficientGroupIso W hW _).inv.hom.hom.hom.left ≫
    (cartesianCoefficientGroupIso W V f hf hz _ hV).hom.hom.hom.hom.left = _
  rw [integralCurveCoefficientGroupIso_inv, cartesianCoefficientGroupIso_hom]

/-- The inverse is exactly the lift of the specified original cartesian map. -/
@[reassoc] theorem cartesianPullbackGroupIso_inv_fst :
    (cartesianPullbackGroupIso W V f hf hz hW hV).inv.hom.hom.hom.left ≫
      pullback.fst (integralCurveStructure W)
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) = f := by
  have he : (cartesianPullbackGroupIso W V f hf hz hW hV).hom.hom.hom.hom.left ≫ f =
      pullback.fst (integralCurveStructure W)
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
    rw [cartesianPullbackGroupIso_hom, Category.assoc, cartesianCoefficientIso_map,
      ← integralCurveCoefficientBaseChangeIso_fst W,
      (integralCurveCoefficientBaseChangeIso W).inv_hom_id_assoc]
  have hi := congrArg (fun k ↦ k.hom.hom.hom.left)
    (cartesianPullbackGroupIso W V f hf hz hW hV).inv_hom_id
  change (cartesianPullbackGroupIso W V f hf hz hW hV).inv.hom.hom.hom.left ≫
    (cartesianPullbackGroupIso W V f hf hz hW hV).hom.hom.hom.hom.left = 𝟙 _ at hi
  rw [← he, ← Category.assoc, hi, Category.id_comp]

end FLT.Mazur.WeierstrassIntegralChart

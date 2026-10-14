/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassCartesianOriginComparison
public import FLT.Mazur.WeierstrassSmoothCoefficientGroupIso
public import FLT.Mazur.WeierstrassSmoothGoodReductionGroup
public import FLT.Mazur.WeierstrassRelativeSmoothDiscriminant

/-!
# Smooth group comparison on a pointed nonsingular Cartesian cubic

The source cubic may have bad reduction. Only the chosen changed cubic needs
unit discriminant: its Cartesian comparison proves good reduction of the
changed equation, and the smooth coefficient comparison supplies the group law.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (V : WeierstrassCurve S)
  (f : integralCurve V ⟶ integralCurve W)
  (hf : IsPullback f (integralCurveStructure V) (integralCurveStructure W)
    (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  (hz : integralCurveZero V ≫ f =
    Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ integralCurveZero W)
  (hV : IsUnit V.Δ)
local notation "U" => W.map (algebraMap R S)

include hf hV in
/-- A nonsingular Cartesian model forces the changed original equation to be nonsingular. -/
theorem cartesianCoefficient_isUnit_discriminant : IsUnit (U).Δ := by
  let _ := integralCurveStructure_smooth V hV
  let _ : Smooth (integralCurveStructure U) := by
    rw [← cartesianCoefficientIso_over W V f hf]
    infer_instance
  let _ : Smooth (chartStructure U 2) := by
    rw [← integralCurveChart_structure]
    infer_instance
  let _ := isElliptic_of_relative_smooth_affineChart U
  exact WeierstrassCurve.isUnit_Δ U

/-- The actual smooth pullback group is the independently chosen nonsingular cubic group. -/
irreducible_def cartesianSmoothPullbackGroupIso :
    originalSmoothBaseChangeGroup S W ≅ integralCurveGroup V hV :=
  (originalSmoothCoefficientGroupIso S W).symm ≪≫
    integralSmoothGoodReductionGroupIso U
      (cartesianCoefficient_isUnit_discriminant W V f hf hV) ≪≫
    cartesianCoefficientGroupIso W V f hf hz
      (cartesianCoefficient_isUnit_discriminant W V f hf hV) hV

/-- Its forward morphism retains the actual smooth and pointed Cartesian comparisons. -/
theorem cartesianSmoothPullbackGroupIso_hom :
    (cartesianSmoothPullbackGroupIso W V f hf hz hV).hom.hom.hom.hom.left =
      (originalSmoothCoefficientIso S W).inv ≫ (integralSmoothOpen U).ι ≫
        (cartesianCoefficientIso W V f hf).hom := by
  rw [cartesianSmoothPullbackGroupIso_def, cartesianCoefficientGroupIso_def]
  rfl

/-- The forward comparison retains the projection to the original whole cubic. -/
@[reassoc] theorem cartesianSmoothPullbackGroupIso_hom_map :
    (cartesianSmoothPullbackGroupIso W V f hf hz hV).hom.hom.hom.hom.left ≫ f =
      pullback.fst (integralSmoothStructure W)
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) ≫ (integralSmoothOpen W).ι := by
  rw [cartesianSmoothPullbackGroupIso_hom, Category.assoc, Category.assoc,
    cartesianCoefficientIso_map, ← originalSmoothCoefficientMap_inclusion,
    ← originalSmoothCoefficientIso_fst, Category.assoc, Iso.inv_hom_id_assoc]

/-- The inverse projects to the specified original Cartesian map, with no new curve choice. -/
@[reassoc] theorem cartesianSmoothPullbackGroupIso_inv_fst :
    (cartesianSmoothPullbackGroupIso W V f hf hz hV).inv.hom.hom.hom.left ≫
      pullback.fst (integralSmoothStructure W)
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) ≫ (integralSmoothOpen W).ι = f := by
  rw [← cartesianSmoothPullbackGroupIso_hom_map W V f hf hz hV]
  have hi := congrArg (fun k ↦ k.hom.hom.hom.left)
    (cartesianSmoothPullbackGroupIso W V f hf hz hV).inv_hom_id
  change (cartesianSmoothPullbackGroupIso W V f hf hz hV).inv.hom.hom.hom.left ≫
    (cartesianSmoothPullbackGroupIso W V f hf hz hV).hom.hom.hom.hom.left = 𝟙 _ at hi
  rw [← Category.assoc, hi, Category.id_comp]

end FLT.Mazur.WeierstrassIntegralChart

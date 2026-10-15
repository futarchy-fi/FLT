/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonComponentCoordinateScaling
public import FLT.Mazur.PolygonPinchingCompleteClosedComparison
import all FLT.Mazur.PolygonPinchingCompleteClosedComparison

/-!
# Coordinate adjustment of the full original closed comparison

Independent projective scalings descend through the original pinching and
adjust the complete closed comparison. Every singular section remains fixed;
the comparison retains the prescribed Laurent scaling on each smooth torus.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonPinching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completeClosedFiberInclusion pinchingCompleteClosedIso polygonCoordinateScaling
variable (K : Type) [Field K] (n : ℕ) (hn : 2 ≤ n) [NeZero n]
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (hp : IsPushout (toComponents K n (by omega)) (toNodes K n) p q)
  (a : Fin n → Kˣ)
local notation "π" => exactVeroneseProjToBase K n hn
local notation "N" => PolygonCyclicAtlas.normalization K n hn
local notation "Q" => PolygonCyclicAtlas.nodes K n hn
local notation "c" => completeClosedFiberInclusion K n hn
local notation "s" => polygonCoordinateScalingIso K (by omega) p q hp a

/-- The original full closed comparison with independently prescribed component coordinates. -/
def adjustedPinchingCompleteClosedIso : C.left ≅ pullback π (completeClosedBase K) :=
  (Over.forget _).mapIso s ≪≫ pinchingCompleteClosedIso K n hn p q hp

/-- The adjusted full closed comparison is over the original coefficient field. -/
@[reassoc] theorem adjustedPinchingCompleteClosedIso_snd :
    (adjustedPinchingCompleteClosedIso K n hn p q hp a).hom ≫ pullback.snd _ _ = C.hom := by
  rw [adjustedPinchingCompleteClosedIso, Iso.trans_hom, Category.assoc,
    pinchingCompleteClosedIso_snd]
  exact (s).hom.w

/-- The entire projective component retains its exact specified scalar correction. -/
@[reassoc] theorem adjustedPinchingCompleteClosedIso_component (i : Fin n) :
    (componentι K n i ≫ p).left ≫
        (adjustedPinchingCompleteClosedIso K n hn p q hp a).hom ≫ pullback.fst _ _ =
      ProjectiveLine.scaling K (a i) ≫ (componentι K n i ≫ N).left ≫ c := by
  have H := congrArg Over.Hom.left
    (componentι_polygonCoordinateScaling K (by omega) p q hp a i)
  have H' : (componentι K n i ≫ p).left ≫ (s).hom.left =
      ProjectiveLine.scaling K (a i) ≫ (componentι K n i ≫ p).left := by
    simpa only [Over.comp_left, Category.assoc, polygonCoordinateScalingIso_hom,
      ProjectiveLine.scalingOver, Over.homMk_left] using H
  rw [adjustedPinchingCompleteClosedIso, Iso.trans_hom, Category.assoc]
  change (componentι K n i ≫ p).left ≫ (s).hom.left ≫ _ ≫ _ = _
  rw [← Category.assoc, H', Category.assoc, pinchingCompleteClosedIso_component]

/-- The adjustment fixes every original singular section in the complete target. -/
@[reassoc] theorem adjustedPinchingCompleteClosedIso_node (i : Fin n) :
    (nodeι K n i ≫ q).left ≫
        (adjustedPinchingCompleteClosedIso K n hn p q hp a).hom ≫ pullback.fst _ _ =
      (nodeι K n i ≫ Q).left ≫ c := by
  have H := congrArg Over.Hom.left
    (nodeι_polygonCoordinateScaling K (by omega) p q hp a i)
  have H' : (nodeι K n i ≫ q).left ≫ (s).hom.left = (nodeι K n i ≫ q).left := by
    simpa only [Over.comp_left, Category.assoc, polygonCoordinateScalingIso_hom,
      ProjectiveLine.scalingOver, Over.homMk_left] using H
  rw [adjustedPinchingCompleteClosedIso, Iso.trans_hom, Category.assoc]
  change (nodeι K n i ≫ q).left ≫ (s).hom.left ≫ _ ≫ _ = _
  rw [← Category.assoc, H', pinchingCompleteClosedIso_node]

/-- Restriction to the full component torus keeps the original Laurent coordinate map. -/
@[reassoc] theorem adjustedPinchingCompleteClosedIso_torus (i : Fin n) :
    (torusToComponent K).left ≫ (componentι K n i ≫ p).left ≫
        (adjustedPinchingCompleteClosedIso K n hn p q hp a).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.scaling (a i)).toRingHom) ≫
        (torusToComponent K).left ≫ (componentι K n i ≫ N).left ≫ c := by
  rw [adjustedPinchingCompleteClosedIso_component,
    torusToComponent_coordinateScaling_assoc, Category.assoc]

/-- Inverse coordinate adjustment cancels the entire original arithmetic Laurent scaling. -/
@[reassoc] theorem adjustedPinchingCompleteClosedIso_scaledTorus
    (i : Fin n) (b : Kˣ) (ha : a i = b⁻¹) :
    Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.scaling b).toRingHom) ≫
        (torusToComponent K).left ≫ (componentι K n i ≫ p).left ≫
          (adjustedPinchingCompleteClosedIso K n hn p q hp a).hom ≫ pullback.fst _ _ =
      (torusToComponent K).left ≫ (componentι K n i ≫ N).left ≫ c := by
  rw [← Category.assoc (Spec.map _), ← torusToComponent_coordinateScaling,
    Category.assoc, adjustedPinchingCompleteClosedIso_component]
  have H : ProjectiveLine.scaling K b ≫ ProjectiveLine.scaling K (a i) = 𝟙 _ := by
    rw [← ProjectiveLine.scaling_mul, ha, mul_inv_cancel, ProjectiveLine.scaling_one]
  rw [← Category.assoc (ProjectiveLine.scaling K b), H, Category.id_comp]

end FLT.Mazur.PolygonInfinitesimalStages

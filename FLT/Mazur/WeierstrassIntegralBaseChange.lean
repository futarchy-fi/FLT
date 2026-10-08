/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassChartBaseChangeSquare
public import FLT.Mazur.WeierstrassCoefficientChartPreimage

/-!
# The integral Weierstrass cubic commutes with arbitrary base change

The actual coefficient morphism has Cartesian affine chart squares. Descent
along the original cubic atlas identifies the whole coefficient-extended cubic
with the categorical fiber product, without a flatness or discriminant hypothesis.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

/-- The actual coefficient square of the glued cubics is Cartesian. -/
theorem integralCoefficient_isPullback :
    IsPullback (integralCoefficientMorphism (S := S) W)
      (integralCurveStructure (W.map (algebraMap R S))) (integralCurveStructure W)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  apply Scheme.isPullback_of_openCover _ _ _ _ (integralCurveOpenCover W)
  intro i
  have h := integralCoefficientChart_isPullback (S := S) W i.down
  have ha : IsPullback (chartCoefficientMorphism (S := S) W i.down)
      (integralCurveChart (W.map (algebraMap R S)) i.down ≫
        integralCurveStructure (W.map (algebraMap R S)))
      (integralCurveChart W i.down ≫ integralCurveStructure W)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
    simpa only [integralCurveChart_structure] using chartCoefficient_isPullback (S := S) W i.down
  refine ha.of_iso h.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
    (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl) (by simp)
  · change _ ≫ 𝟙 _ = h.isoPullback.hom ≫ pullback.snd _ _
    rw [Category.comp_id, h.isoPullback_hom_snd]
  · change (_ ≫ integralCurveStructure (W.map (algebraMap R S))) ≫ 𝟙 _ =
      h.isoPullback.hom ≫ pullback.fst _ _ ≫ integralCurveStructure (W.map (algebraMap R S))
    rw [Category.comp_id, ← Category.assoc, h.isoPullback_hom_fst]

/-- Formation of the actual integral cubic commutes with every coefficient extension. -/
def integralCurveCoefficientBaseChangeIso : integralCurve (W.map (algebraMap R S)) ≅
    pullback (integralCurveStructure W) (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  (integralCoefficient_isPullback W).isoPullback

/-- The first projection of the comparison is the constructed global coefficient map. -/
@[reassoc] theorem integralCurveCoefficientBaseChangeIso_fst :
    (integralCurveCoefficientBaseChangeIso (S := S) W).hom ≫ pullback.fst _ _ =
      integralCoefficientMorphism W :=
  (integralCoefficient_isPullback W).isoPullback_hom_fst

/-- The second projection of the comparison is the specialized cubic's structure map. -/
@[reassoc] theorem integralCurveCoefficientBaseChangeIso_snd :
    (integralCurveCoefficientBaseChangeIso (S := S) W).hom ≫ pullback.snd _ _ =
      integralCurveStructure (W.map (algebraMap R S)) :=
  (integralCoefficient_isPullback W).isoPullback_hom_snd

end FLT.Mazur.WeierstrassIntegralChart

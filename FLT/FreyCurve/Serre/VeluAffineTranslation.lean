/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluAffineSmoothCoordinates

/-!
# Actual translations by the original affine point group

Each original affine point gives the existing automorphism of the whole cubic.
Its action over any field extension is the original affine group addition.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] (E : WeierstrassCurve K)

/-- Every original affine point supplies an actual smooth section over the same field. -/
theorem affineSmoothPoint_section (P : E.toAffine.Point) :
    affineSmoothPoint E P ≫ integralSmoothStructure E = 𝟙 _ := by
  rw [affineSmoothPoint_structure]
  exact Spec.map_id _

/-- Translation by an original affine point on the whole original cubic. -/
def affineTranslationIso (P : E.toAffine.Point) : integralCurve E ≅ integralCurve E :=
  integralCurveTranslationIso E (affineSmoothPoint E P) (affineSmoothPoint_section E P)

/-- The translation preserves the original coefficient map. -/
@[reassoc] theorem affineTranslationIso_structure (P : E.toAffine.Point) :
    (affineTranslationIso E P).hom ≫ integralCurveStructure E = integralCurveStructure E :=
  integralCurveTranslation_structure E _ (affineSmoothPoint_section E P)

/-- Evaluation of the actual translation on an arbitrary scheme-valued point. -/
theorem affineTranslationIso_point (P : E.toAffine.Point) {X : Scheme}
    (f : X ⟶ integralCurve E) :
    f ≫ (affineTranslationIso E P).hom =
      leftSmoothPointAddition E (f ≫ integralCurveStructure E ≫ affineSmoothPoint E P) f
        (by rw [Category.assoc, Category.assoc, affineSmoothPoint_section, Category.comp_id]) := by
  change f ≫ integralCurveTranslation E _ (affineSmoothPoint_section E P) = _
  rw [integralCurveTranslation, ← leftSmoothPointAddition_comp]
  simp only [Category.comp_id]

variable [DecidableEq K] {L : Type} [Field L] [Algebra K L] [DecidableEq L]

/-- The original point under the specified field extension. -/
def affineScalarPoint (P : E.toAffine.Point) : (E.map (algebraMap K L)).toAffine.Point :=
  Affine.Point.map (W' := E.toAffine) (Algebra.ofId K L) P

/-- On original field-valued points the automorphism is precisely classical translation. -/
theorem affineTranslationIso_action (P : E.toAffine.Point)
    (Q : (E.map (algebraMap K L)).toAffine.Point) :
    (affineSmoothPoint E Q ≫ (integralSmoothOpen E).ι) ≫
        (affineTranslationIso E P).hom =
      affineSmoothPoint E
        (affineScalarPoint E P + Q) ≫
          (integralSmoothOpen E).ι := by
  rw [affineTranslationIso_point]
  have hb : (affineSmoothPoint E Q ≫ (integralSmoothOpen E).ι) ≫
      integralCurveStructure E = Spec.map (CommRingCat.ofHom (algebraMap K L)) :=
    affineSmoothPoint_structure E Q
  have hp : Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ affineSmoothPoint E P =
      affineSmoothPoint E (affineScalarPoint E P) := affineSmoothPoint_base E P
  have he : (affineSmoothPoint E Q ≫ (integralSmoothOpen E).ι) ≫
      integralCurveStructure E ≫ affineSmoothPoint E P =
      affineSmoothPoint E (affineScalarPoint E P) := by
    rw [← Category.assoc, hb, hp]
  simpa only [he] using affineSmoothPoint_action E (affineScalarPoint E P) Q

end WeierstrassCurve.Velu

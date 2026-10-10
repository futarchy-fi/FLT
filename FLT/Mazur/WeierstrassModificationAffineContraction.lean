/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationGluing

/-!
# The actual first modification contracts to the original affine cubic

The original coordinate maps already land in the affine cubic chart. They
glue there, and composing with its open inclusion recovers the existing
projective-cubic contraction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)

/-- The glued local modification maps to the original affine cubic by its coordinates. -/
def affineContraction : modification W s b3 b4 b6 ⟶
    Spec (.of (WeierstrassIntegralChart.Coordinate W 2)) :=
  pushout.desc (Spec.map (CommRingCat.ofHom (fromOriginal W s b3 b4 b6 h3 h4 h6).toRingHom))
    (Spec.map (CommRingCat.ofHom
      (WeierstrassDilatation.fromOriginal W s b3 b4 b6 h3 h4 h6).toRingHom)) (by
        apply (cancel_mono (WeierstrassIntegralChart.integralCurveChart W 2)).mp
        simpa only [Category.assoc, overlapToDivided, toCurve,
          WeierstrassDilatation.toCurve] using (overlapIso_toCurve W s b3 b4 b6 h3 h4 h6).symm)

/-- The affine contraction retains the original x-direction coordinate substitution. -/
@[reassoc (attr := simp)] theorem xChart_affineContraction :
    xChart W s b3 b4 b6 ≫ affineContraction W s b3 b4 b6 h3 h4 h6 =
      Spec.map (CommRingCat.ofHom (fromOriginal W s b3 b4 b6 h3 h4 h6).toRingHom) :=
  pushout.inl_desc _ _ _

/-- The affine contraction retains the original divided coordinate substitution. -/
@[reassoc (attr := simp)] theorem dividedChart_affineContraction :
    dividedChart W s b3 b4 b6 ≫ affineContraction W s b3 b4 b6 h3 h4 h6 =
      Spec.map (CommRingCat.ofHom
        (WeierstrassDilatation.fromOriginal W s b3 b4 b6 h3 h4 h6).toRingHom) :=
  pushout.inr_desc _ _ _

/-- The affine factorization is exactly the existing original-cubic contraction. -/
@[reassoc] theorem affineContraction_toCurve :
    affineContraction W s b3 b4 b6 h3 h4 h6 ≫
        WeierstrassIntegralChart.integralCurveChart W 2 =
      contraction W s b3 b4 b6 h3 h4 h6 := by
  apply pushout.hom_ext
  · change xChart W s b3 b4 b6 ≫ _ = xChart W s b3 b4 b6 ≫ _
    rw [xChart_affineContraction_assoc, xChart_contraction]
    rfl
  · change dividedChart W s b3 b4 b6 ≫ _ = dividedChart W s b3 b4 b6 ≫ _
    rw [dividedChart_affineContraction_assoc, dividedChart_contraction]
    rfl

end FLT.Mazur.WeierstrassModificationX

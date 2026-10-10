/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationReesProjGluing
public import FLT.Mazur.BlowupReesContraction

/-!
# The global Rees Proj comparison retains the original cubic contraction

The glued map from the actual modification to Rees Proj is over the original
cubic, using the canonical Proj-to-degree-zero map and the original coefficient
ring identification. No global isomorphism or properness is assumed here.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassModificationReesCoordinates

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)

local notation "I" => WeierstrassDilatation.modificationCenter W s

/-- The horizontal Proj inclusion contracts through its original coordinate functions. -/
@[reassoc] theorem horizontalProjInclusion_contraction :
    horizontalProjInclusion W s ≫ BlowupRees.contraction I =
      Spec.map (CommRingCat.ofHom (horizontalOriginalMap W s)) :=
  BlowupRees.fractionChartInclusion_contraction I _ _

/-- The scale Proj inclusion contracts through its original coordinate functions. -/
@[reassoc] theorem scaleProjInclusion_contraction :
    scaleProjInclusion W s ≫ BlowupRees.contraction I =
      Spec.map (CommRingCat.ofHom (scaleOriginalMap W s)) :=
  BlowupRees.fractionChartInclusion_contraction I _ _

variable [IsDomain R]

/-- The glued fraction-atlas map retains the canonical original cubic contraction. -/
@[reassoc] theorem fractionAtlasToProj_contraction :
    fractionAtlasToProj W s b3 b4 b6 h3 h4 h6 hs ≫ BlowupRees.contraction I ≫
      WeierstrassIntegralChart.integralCurveChart W 2 =
        fractionContraction W s b3 b4 b6 h3 h4 h6 hs := by
  apply pushout.hom_ext
  · change horizontalChart W s b3 b4 b6 h3 h4 h6 hs ≫ _ =
      horizontalChart W s b3 b4 b6 h3 h4 h6 hs ≫ _
    rw [horizontalChart_toProj_assoc, horizontalProjInclusion_contraction_assoc,
      horizontalChart_contraction]
  · change scaleChart W s b3 b4 b6 h3 h4 h6 hs ≫ _ =
      scaleChart W s b3 b4 b6 h3 h4 h6 hs ≫ _
    rw [scaleChart_toProj_assoc, scaleProjInclusion_contraction_assoc, scaleChart_contraction]

/-- The actual equation modification maps to Rees Proj over its original cubic. -/
@[reassoc] theorem modificationToProj_contraction :
    modificationToProj W s b3 b4 b6 h3 h4 h6 hs ≫ BlowupRees.contraction I ≫
      WeierstrassIntegralChart.integralCurveChart W 2 =
        WeierstrassModificationX.contraction W s b3 b4 b6 h3 h4 h6 := by
  apply (cancel_epi (fractionAtlasIso W s b3 b4 b6 h3 h4 h6 hs).hom).mp
  rw [fractionAtlasIso_toProj_assoc, fractionAtlasToProj_contraction]
  rfl

end FLT.Mazur.WeierstrassModificationReesCoordinates

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationReesProjYScale
public import FLT.Mazur.WeierstrassModificationReesYCover

/-!
# The actual fraction atlas maps globally to the original Rees Proj

The proved full overlap square glues the horizontal and scale inclusions.
On the vertical chart the resulting map is its actual Rees Proj inclusion,
as verified on the original two-ratio cover.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassModificationReesCoordinates

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)

/-- The glued actual fraction atlas maps to Proj of the original center's Rees algebra. -/
def fractionAtlasToProj : fractionAtlas W s b3 b4 b6 h3 h4 h6 hs ⟶
    BlowupRees.proj (WeierstrassDilatation.modificationCenter W s) :=
  pushout.desc (horizontalProjInclusion W s) (scaleProjInclusion W s)
    (horizontalOverlap_toProj W s b3 b4 b6 h3 h4 h6 hs).symm

/-- The global Proj map retains the original horizontal chart inclusion. -/
@[reassoc] theorem horizontalChart_toProj :
    horizontalChart W s b3 b4 b6 h3 h4 h6 hs ≫
      fractionAtlasToProj W s b3 b4 b6 h3 h4 h6 hs = horizontalProjInclusion W s :=
  pushout.inl_desc _ _ _

/-- The global Proj map retains the original scale chart inclusion. -/
@[reassoc] theorem scaleChart_toProj :
    scaleChart W s b3 b4 b6 h3 h4 h6 hs ≫
      fractionAtlasToProj W s b3 b4 b6 h3 h4 h6 hs = scaleProjInclusion W s :=
  pushout.inr_desc _ _ _

/-- The entire vertical fraction chart also retains its actual Rees Proj inclusion. -/
@[reassoc] theorem verticalChart_toProj [IsBezout R] :
    verticalChart W s b3 b4 b6 h3 h4 h6 hs ≫
      fractionAtlasToProj W s b3 b4 b6 h3 h4 h6 hs = verticalProjInclusion W s := by
  apply (verticalRatioCover W s b3 b4 b6 h3 h4 h6 hs).hom_ext
  intro i
  change Fin 2 at i
  fin_cases i
  · change verticalScaleInclusion W s ≫ _ = verticalScaleInclusion W s ≫ _
    rw [verticalChart_scale_assoc, scaleChart_toProj, verticalScale_toProj]
  · change verticalHorizontalInclusion W s ≫ _ = verticalHorizontalInclusion W s ≫ _
    rw [verticalChart_horizontal_assoc, horizontalChart_toProj, verticalHorizontal_toProj]

/-- The actual equation modification maps globally to the original Rees Proj. -/
def modificationToProj : WeierstrassModificationX.modification W s b3 b4 b6 ⟶
    BlowupRees.proj (WeierstrassDilatation.modificationCenter W s) :=
  (fractionAtlasIso W s b3 b4 b6 h3 h4 h6 hs).inv ≫
    fractionAtlasToProj W s b3 b4 b6 h3 h4 h6 hs

/-- The global fraction/equation comparison retains the glued Proj map. -/
@[reassoc] theorem fractionAtlasIso_toProj :
    (fractionAtlasIso W s b3 b4 b6 h3 h4 h6 hs).hom ≫
      modificationToProj W s b3 b4 b6 h3 h4 h6 hs =
        fractionAtlasToProj W s b3 b4 b6 h3 h4 h6 hs := by
  rw [modificationToProj, Iso.hom_inv_id_assoc]

end FLT.Mazur.WeierstrassModificationReesCoordinates

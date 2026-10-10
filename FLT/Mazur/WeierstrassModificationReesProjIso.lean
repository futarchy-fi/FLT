/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationReesProjCover
public import FLT.Mazur.WeierstrassModificationReesProjEmbedding
public import FLT.Mazur.WeierstrassModificationReesProjContraction

/-!
# The actual equation modification is the original Rees Proj

The global fraction-atlas map is a surjective open immersion. Its inverse
therefore gives an actual scheme isomorphism, and the equation modification
inherits this comparison over the original cubic contraction.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassModificationReesCoordinates

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)

local notation "I" => WeierstrassDilatation.modificationCenter W s

instance fractionAtlasToProj_isIso :
    IsIso (fractionAtlasToProj W s b3 b4 b6 h3 h4 h6 hs) := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  apply TopologicalSpace.Opens.ext
  exact Set.range_eq_univ.mpr (fractionAtlasToProj_surjective W s b3 b4 b6 h3 h4 h6 hs)

/-- The original fraction atlas is globally isomorphic to the original center's Rees Proj. -/
def fractionAtlasProjIso : fractionAtlas W s b3 b4 b6 h3 h4 h6 hs ≅ BlowupRees.proj I :=
  asIso (fractionAtlasToProj W s b3 b4 b6 h3 h4 h6 hs)

instance modificationToProj_isIso : IsIso (modificationToProj W s b3 b4 b6 h3 h4 h6 hs) := by
  rw [modificationToProj]
  infer_instance

/-- The actual equation modification is the projective spectrum of the original Rees algebra. -/
def modificationProjIso :
    WeierstrassModificationX.modification W s b3 b4 b6 ≅ BlowupRees.proj I :=
  asIso (modificationToProj W s b3 b4 b6 h3 h4 h6 hs)

/-- The global isomorphism retains the original contraction to the integral cubic. -/
@[reassoc] theorem modificationProjIso_contraction :
    (modificationProjIso W s b3 b4 b6 h3 h4 h6 hs).hom ≫ BlowupRees.contraction I ≫
      WeierstrassIntegralChart.integralCurveChart W 2 =
        WeierstrassModificationX.contraction W s b3 b4 b6 h3 h4 h6 :=
  modificationToProj_contraction W s b3 b4 b6 h3 h4 h6 hs

/-- The inverse Proj comparison also retains the original cubic contraction. -/
@[reassoc] theorem modificationProjIso_inv_contraction :
    (modificationProjIso W s b3 b4 b6 h3 h4 h6 hs).inv ≫
      WeierstrassModificationX.contraction W s b3 b4 b6 h3 h4 h6 =
        BlowupRees.contraction I ≫ WeierstrassIntegralChart.integralCurveChart W 2 := by
  rw [← modificationProjIso_contraction W s b3 b4 b6 h3 h4 h6 hs,
    Iso.inv_hom_id_assoc]

end FLT.Mazur.WeierstrassModificationReesCoordinates

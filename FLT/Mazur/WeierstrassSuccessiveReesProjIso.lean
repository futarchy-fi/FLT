/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveReesCover
public import FLT.Mazur.WeierstrassSuccessiveReesProjEmbedding

/-!
# The whole successive equation modification is its Rees Proj

The two fraction charts cover the entire Rees scheme, and the proved full
intersection gives an open immersion. Thus the actual local replacement
is isomorphic to the Rees Proj of the preceding center.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveRees

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] [IsDomain R]
  (W : WeierstrassCurve R) (s π b3 b4 b6 : R) (hπ : π ≠ 0)
local notation "I" => WeierstrassSuccessiveX.modificationCenter W s π b3 b4 b6

/-- Every point of the Rees scheme is reached by the actual two-chart fraction atlas. -/
theorem fractionAtlasToProj_surjective :
    Function.Surjective (fractionAtlasToProj W s π b3 b4 b6 hπ) := by
  intro z
  rcases fraction_charts_cover W s π b3 b4 b6 z with ⟨a, ha⟩ | ⟨a, ha⟩
  · refine ⟨scaleChart W s π b3 b4 b6 hπ a, ?_⟩
    change (scaleChart W s π b3 b4 b6 hπ ≫ fractionAtlasToProj W s π b3 b4 b6 hπ) a = z
    rwa [scaleChart_toProj]
  · refine ⟨horizontalChart W s π b3 b4 b6 hπ a, ?_⟩
    change (horizontalChart W s π b3 b4 b6 hπ ≫ fractionAtlasToProj W s π b3 b4 b6 hπ) a = z
    rwa [horizontalChart_toProj]

instance fractionAtlasToProj_isIso : IsIso (fractionAtlasToProj W s π b3 b4 b6 hπ) := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  apply TopologicalSpace.Opens.ext
  exact Set.range_eq_univ.mpr (fractionAtlasToProj_surjective W s π b3 b4 b6 hπ)

/-- The whole fraction atlas is the original center's Rees Proj. -/
def fractionAtlasProjIso : fractionAtlas W s π b3 b4 b6 hπ ≅ BlowupRees.proj I :=
  asIso (fractionAtlasToProj W s π b3 b4 b6 hπ)

instance modificationToProj_isIso : IsIso (modificationToProj W s π b3 b4 b6 hπ) := by
  rw [modificationToProj]
  infer_instance

/-- The actual successive equation modification is the entire Rees projective spectrum. -/
def modificationProjIso :
    WeierstrassSuccessiveX.modification W s π b3 b4 b6 ≅ BlowupRees.proj I :=
  asIso (modificationToProj W s π b3 b4 b6 hπ)

end FLT.Mazur.WeierstrassSuccessiveRees

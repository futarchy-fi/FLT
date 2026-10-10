/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGlobalModificationOriginalOpen
public import FLT.Mazur.WeierstrassModificationCenterSmooth

/-!
# The entire original smooth open is unchanged by the global modification

Every original smooth affine point avoids the modification center. The
complete principal-open comparisons and unchanged infinity chart therefore
identify the entire inverse image of the original relative smooth locus.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassGlobalModification
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)
open WeierstrassIntegralChart

/-- The actual contraction is an isomorphism over the full original relative smooth open. -/
theorem smooth_restrict_isIso :
    IsIso (contraction W s b3 b4 b6 h3 h4 h6 hs ∣_ integralSmoothOpen W) := by
  apply SchemeUnchangedOpen.isIso_of_neighborhoods
  intro z hz
  obtain ⟨p, hp⟩ | ⟨p, hp⟩ := integralCurve_yz_cover W z
  · refine ⟨(integralCurveChart W 1).opensRange, ⟨p, hp⟩, ?_⟩
    exact SchemeUnchangedOpen.isIso_of_identity_pullback _ _ _
      (infinity_isPullback W s b3 b4 b6 h3 h4 h6 hs)
  · have hp' : p ∈ (chartStructure W 2).smoothLocus := by
      rw [← integralCurveChart_preimage_smooth]
      change integralCurveChart W 2 p ∈ integralSmoothOpen W
      rwa [hp]
    have hn := modificationCenter_not_le_of_smooth W s b3 b4 h3 h4 p hp'
    change ¬ ∀ f, f ∈ WeierstrassDilatation.modificationCenter W s → f ∈ p.asIdeal at hn
    push Not at hn
    obtain ⟨f, hf, hfp⟩ := hn
    refine ⟨(PrincipalAffineRefinement.inclusion f ≫ integralCurveChart W 2).opensRange,
      ?_, originalOpen_restrict_isIso W s b3 b4 b6 h3 h4 h6 hs f hf⟩
    have hm : p ∈ Set.range (PrincipalAffineRefinement.inclusion f) := by
      rw [PrincipalAffineRefinement.range_inclusion]
      exact hfp
    obtain ⟨q, rfl⟩ := hm
    exact ⟨q, hp⟩

/-- The full unchanged smooth inverse image, with its actual contraction map. -/
def smoothPreimageIso :
    (contraction W s b3 b4 b6 h3 h4 h6 hs ⁻¹ᵁ integralSmoothOpen W).toScheme ≅
      (integralSmoothOpen W).toScheme := by
  let _ := smooth_restrict_isIso W s b3 b4 b6 h3 h4 h6 hs
  exact asIso (contraction W s b3 b4 b6 h3 h4 h6 hs ∣_ integralSmoothOpen W)

/-- The smooth comparison retains the actual original global contraction. -/
@[reassoc] theorem smoothPreimageIso_hom_inclusion :
    (smoothPreimageIso W s b3 b4 b6 h3 h4 h6 hs).hom ≫ (integralSmoothOpen W).ι =
      (contraction W s b3 b4 b6 h3 h4 h6 hs ⁻¹ᵁ integralSmoothOpen W).ι ≫
        contraction W s b3 b4 b6 h3 h4 h6 hs :=
  morphismRestrict_ι _ _

end FLT.Mazur.WeierstrassGlobalModification

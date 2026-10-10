/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteSmoothOpen
public import FLT.Mazur.WeierstrassDividedGlobalFiniteProper
public import FLT.Mazur.SchemeUnchangedOpenPullback

/-!
# Entire original smooth opens in every finite global model

The full finite affine pullback preserves the original affine smooth open,
and the full infinity pullback is unchanged. Together they identify the
complete inverse image of the original relative smooth locus at every depth.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
open WeierstrassIntegralChart

/-- The whole finite contraction is an isomorphism over the entire original smooth open. -/
theorem finiteGlobal_originalSmooth_isIso :
    IsIso (finiteGlobalContraction hπ data j hj ∣_ integralSmoothOpen W) := by
  apply SchemeUnchangedOpen.isIso_of_neighborhoods
  intro z hz
  obtain ⟨p, hp⟩ | ⟨p, hp⟩ := integralCurve_yz_cover W z
  · refine ⟨(integralCurveChart W 1).opensRange, ⟨p, hp⟩, ?_⟩
    exact SchemeUnchangedOpen.isIso_of_identity_pullback _ _ _
      (finiteInfinity_isPullback hπ data j hj)
  · have hp' : p ∈ (chartStructure W 2).smoothLocus := by
      rw [← integralCurveChart_preimage_smooth]
      change integralCurveChart W 2 p ∈ integralSmoothOpen W
      rwa [hp]
    refine ⟨((chartStructure W 2).smoothLocus.ι ≫ integralCurveChart W 2).opensRange,
      ⟨⟨p, hp'⟩, hp⟩, ?_⟩
    exact SchemeUnchangedOpen.isIso_of_chart_pullback _ _ _ _
      (finiteLocal_isPullback hπ data j hj) _ (finiteToAffine_originalSmooth_isIso hπ data j hj)

/-- The full original smooth inverse image with its actual finite contraction map. -/
def finiteGlobalSmoothPreimageIso :
    (finiteGlobalContraction hπ data j hj ⁻¹ᵁ integralSmoothOpen W).toScheme ≅
      (integralSmoothOpen W).toScheme := by
  let _ := finiteGlobal_originalSmooth_isIso hπ data j hj
  exact asIso (finiteGlobalContraction hπ data j hj ∣_ integralSmoothOpen W)

/-- The smooth comparison retains the actual original global contraction. -/
@[reassoc] theorem finiteGlobalSmoothPreimageIso_hom_inclusion :
    (finiteGlobalSmoothPreimageIso hπ data j hj).hom ≫ (integralSmoothOpen W).ι =
      (finiteGlobalContraction hπ data j hj ⁻¹ᵁ integralSmoothOpen W).ι ≫
        finiteGlobalContraction hπ data j hj := morphismRestrict_ι _ _

end FLT.Mazur.WeierstrassDividedDepth

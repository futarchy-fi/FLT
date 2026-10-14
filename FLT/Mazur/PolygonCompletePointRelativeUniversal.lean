/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointGlobalFunctions
public import FLT.Mazur.AffineFunctionUniversal

/-!
# Affinization on every affine open of the original contraction target

The original global cubic morphism restricts to the canonical affinization
over every affine target open, with unique factorization into affine schemes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "W" => completePointWeierstrassCurve K n h i
local notation "g" => completePointToIntegralCubic K n h i

/-- Every original target-open restriction preserves its actual global functions. -/
theorem completePointCubicRestriction_appTop_isIso (U : (integralCurve (W)).Opens) :
    IsIso (((g) ∣_ U).appTop) := by
  rw [morphismRestrict_appTop]
  let _ := completePointToIntegralCubic_app_isIso K n h i (U.ι ''ᵁ ⊤)
  infer_instance

/-- Every affine target open is the spectrum of the full inverse-image function ring. -/
def completePointCubicRestrictionSpectrumIso (U : (integralCurve (W)).Opens)
    (hU : IsAffineOpen U) : Spec Γ(((g) ⁻¹ᵁ U).toScheme, ⊤) ≅ U.toScheme := by
  let _ : IsAffine U.toScheme := hU
  let _ := completePointCubicRestriction_appTop_isIso K n h i U
  exact AffineFunctionUniversal.spectrumIso ((g) ∣_ U)

/-- The spectrum identification retains the original restricted contraction. -/
@[reassoc] theorem completePointCubicRestrictionSpectrumIso_fac
    (U : (integralCurve (W)).Opens) (hU : IsAffineOpen U) :
    ((g) ⁻¹ᵁ U).toScheme.toSpecΓ ≫
        (completePointCubicRestrictionSpectrumIso K n h i U hU).hom = (g) ∣_ U := by
  let _ : IsAffine U.toScheme := hU
  let _ := completePointCubicRestriction_appTop_isIso K n h i U
  exact AffineFunctionUniversal.spectrumIso_fac ((g) ∣_ U)

/-- The actual original contraction has the relative affine universal property on every chart. -/
theorem completePointCubicRestriction_existsUnique_factor
    (U : (integralCurve (W)).Opens) (hU : IsAffineOpen U)
    (T : Scheme) [IsAffine T] (q : ((g) ⁻¹ᵁ U).toScheme ⟶ T) :
    ∃! b : U.toScheme ⟶ T, ((g) ∣_ U) ≫ b = q := by
  let _ : IsAffine U.toScheme := hU
  let _ := completePointCubicRestriction_appTop_isIso K n h i U
  exact AffineFunctionUniversal.existsUnique_factor ((g) ∣_ U) T q

end FLT.Mazur.PolygonInfinitesimalStages

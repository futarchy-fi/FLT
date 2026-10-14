/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeSmoothLocusCartesian
public import FLT.Mazur.WeierstrassLeftSmoothTranslationGraph

/-!
# The exact smooth domain of universal cubic translation

The whole scheme-valued action has smooth output exactly when its second
input is smooth. The proof uses the universal translation isomorphism and
arbitrary base change, so no rational-point or reducedness assumption enters.
-/

public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
local notation "s" => integralSmoothStructure W
local notation "c" => integralCurveStructure W

/-- The second input's smooth inverse image is the relative smooth locus over the parameter. -/
theorem leftSmoothFactorSecond_preimage_smooth :
    pullback.snd (s) (c) ⁻¹ᵁ integralSmoothOpen W =
      (pullback.fst (s) (c)).smoothLocus :=
  smoothLocus_preimage_of_isPullback (IsPullback.of_hasPullback (s) (c)).flip

/-- Universal translation preserves the full smooth open of its arbitrary second input. -/
theorem leftSmoothFactorAddition_preimage_smooth :
    leftSmoothFactorAddition W ⁻¹ᵁ integralSmoothOpen W =
      pullback.snd (s) (c) ⁻¹ᵁ integralSmoothOpen W := by
  let _ : IsIso (leftSmoothTranslationGraph W) := (leftSmoothTranslationIso W).isIso_hom
  rw [← leftSmoothTranslationGraph_snd, Scheme.Hom.comp_preimage,
    leftSmoothFactorSecond_preimage_smooth, Scheme.Hom.preimage_smoothLocus_eq]
  congr 1
  exact leftSmoothTranslationGraph_fst W

/-- The exact same open equality holds on every scheme of compatible inputs. -/
theorem leftSmoothPointAddition_preimage_smooth {X : Scheme.{u}}
    (a : X ⟶ (integralSmoothOpen W).toScheme) (b : X ⟶ integralCurve W)
    (hab : a ≫ (s) = b ≫ (c)) :
    leftSmoothPointAddition W a b hab ⁻¹ᵁ integralSmoothOpen W =
      b ⁻¹ᵁ integralSmoothOpen W := by
  rw [leftSmoothPointAddition, Scheme.Hom.comp_preimage,
    leftSmoothFactorAddition_preimage_smooth, ← Scheme.Hom.comp_preimage, pullback.lift_snd]

end FLT.Mazur.WeierstrassIntegralChart

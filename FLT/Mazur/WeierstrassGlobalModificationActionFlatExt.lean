/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGlobalModificationRegularLiftExt
public import FLT.Mazur.WeierstrassGlobalModificationActionCenter
public import FLT.Mazur.WeierstrassGlobalModificationUnchangedOverlap

/-!
# Uniqueness of the actual local action after flat affine restriction

Any flat affine restriction of an actual cover member retains its regular
principal output center. Its constructed local action is therefore the unique
lift of its original action, including at exceptional outputs. The unchanged
X and Y cases use their full pullback squares.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassGlobalModification

open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R B : Type u} [CommRing R] [IsDomain R] [IsBezout R] [CommRing B]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)
  (i : (smoothActionCover W s b3 b4 b6 h3 h4 h6 hs).I₀)

/-- Flat affine restrictions of affine-output members have a unique contracted-action lift. -/
theorem smoothActionLocal_flat_unique_affine
    (hi : modifiedSmoothOutputIndex W (originalInputContraction W s i.1) i.2 = 2)
    (p : Spec (.of B) ⟶ Spec ((smoothActionCover W s b3 b4 b6 h3 h4 h6 hs).X i)) [Flat p]
    (f : Spec (.of B) ⟶ model W s b3 b4 b6 h3 h4 h6 hs)
    (hf : f ≫ contraction W s b3 b4 b6 h3 h4 h6 hs =
      p ≫ smoothActionLocal W s b3 b4 b6 h3 h4 h6 hs i ≫
        contraction W s b3 b4 b6 h3 h4 h6 hs) :
    f = p ≫ smoothActionLocal W s b3 b4 b6 h3 h4 h6 hs i := by
  let ψ := affineChartRingHom p
  let φ := modifiedSmoothOutputHomAt W (originalInputContraction W s i.1) i.2 2 hi
  let d := smoothActionDenominator W s b3 b4 b6 h3 h4 h6 hs i
  have hp : Spec.map (CommRingCat.ofHom ψ) = p := affineChartRingHom_spec p
  have hflat : ψ.Flat := by
    apply (Flat.SpecMap_iff (f := CommRingCat.ofHom ψ)).mp
    rw [hp]
    infer_instance
  have hI : (modificationChartCenter W s 2).map (ψ.comp φ) = Ideal.span {ψ d} :=
    RegularCenter.mapped_center (modificationChartCenter W s 2) φ d
      (smoothActionOutput_center W s b3 b4 b6 h3 h4 h6 hs i hi) ψ
  have hd : IsRegular (ψ d) := flatRingHom_isRegular ψ hflat
    (smoothActionDenominator_regular W s b3 b4 b6 h3 h4 h6 hs i)
  have hc : (p ≫ smoothActionLocal W s b3 b4 b6 h3 h4 h6 hs i) ≫
      contraction W s b3 b4 b6 h3 h4 h6 hs =
        Spec.map (CommRingCat.ofHom (ψ.comp φ)) ≫ integralCurveChart W 2 := by
    rw [Category.assoc, smoothActionLocal_affine_contraction W s b3 b4 b6 h3 h4 h6 hs i hi,
      CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hp]
  apply regular_center_lift_ext W s b3 b4 b6 h3 h4 h6 hs (ψ.comp φ) (ψ d) hI hd
    f (p ≫ smoothActionLocal W s b3 b4 b6 h3 h4 h6 hs i)
  · exact hf.trans ((Category.assoc _ _ _).symm.trans hc)
  · exact hc

/-- Every actual local action is unique after any flat affine restriction of its source. -/
theorem smoothActionLocal_flat_unique
    (p : Spec (.of B) ⟶ Spec ((smoothActionCover W s b3 b4 b6 h3 h4 h6 hs).X i)) [Flat p]
    (f : Spec (.of B) ⟶ model W s b3 b4 b6 h3 h4 h6 hs)
    (hf : f ≫ contraction W s b3 b4 b6 h3 h4 h6 hs =
      p ≫ smoothActionLocal W s b3 b4 b6 h3 h4 h6 hs i ≫
        contraction W s b3 b4 b6 h3 h4 h6 hs) :
    f = p ≫ smoothActionLocal W s b3 b4 b6 h3 h4 h6 hs i := by
  by_cases hi : modifiedSmoothOutputIndex W (originalInputContraction W s i.1) i.2 = 2
  · exact smoothActionLocal_flat_unique_affine W s b3 b4 b6 h3 h4 h6 hs i hi p f hf
  · exact smoothActionLocal_unique_unchanged W s b3 b4 b6 h3 h4 h6 hs i hi p f hf

end FLT.Mazur.WeierstrassGlobalModification

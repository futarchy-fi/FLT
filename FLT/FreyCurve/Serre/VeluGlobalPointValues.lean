/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluGlobalRestrictions
public import FLT.FreyCurve.Serre.VeluAffinePointMorphism

/-!
# Values of the global Vélu morphism on the original points

Infinity and the original subgroup go to the original target infinity.
Outside the subgroup the global map gives the original finite coordinate sums.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] [CharZero K] [IsAlgClosed K] [DecidableEq K]
  (E : WeierstrassCurve K) [E.IsElliptic]
  (G : AddSubgroup E.toAffine.Point) [Fintype G]
  (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)

/-- Original infinity maps to original infinity under the global morphism. -/
@[reassoc] theorem veluGlobalMorphism_zero :
    integralCurveZero E ≫ veluGlobalMorphism E G hodd = integralCurveZero (curve E G) := by
  rw [← veluInfinityPointLift_zero E G, Category.assoc, veluGlobalMorphism_infinity]
  exact veluInfinityRegularMorphism_point E G hodd

/-- The negative of each original nonzero kernel point maps to original target infinity. -/
@[reassoc] theorem veluGlobalMorphism_negativeKernel {u v : K}
    (hQ : E.toAffine.Nonsingular u v) (hQG : Affine.Point.some u v hQ ∈ G) :
    (affineSmoothPoint E (-Affine.Point.some u v hQ) ≫ (integralSmoothOpen E).ι) ≫
      veluGlobalMorphism E G hodd = integralCurveZero (curve E G) := by
  rw [← veluTranslatedInfinityPoint_source E G (.some u v hQ), Category.assoc,
    veluGlobalMorphism_translatedInfinity E G hodd hQ hQG]
  exact veluInfinityRegularMorphism_point E G hodd

/-- Each original nonzero kernel point maps to original target infinity. -/
@[reassoc] theorem veluGlobalMorphism_affineKernel {u v : K}
    (hQ : E.toAffine.Nonsingular u v) (hQG : Affine.Point.some u v hQ ∈ G) :
    (affineSmoothPoint E (.some u v hQ) ≫ (integralSmoothOpen E).ι) ≫
      veluGlobalMorphism E G hodd = integralCurveZero (curve E G) := by
  have hn := (Affine.nonsingular_neg u v).mpr hQ
  have hm : Affine.Point.some u (E.toAffine.negY u v) hn ∈ G := G.neg_mem hQG
  have h := veluGlobalMorphism_negativeKernel E G hodd hn hm
  change (affineSmoothPoint E (-(-Affine.Point.some u v hQ)) ≫ _) ≫ _ = _ at h
  simpa only [neg_neg] using h

/-- Every point in the original subgroup maps to the actual target identity section. -/
@[reassoc] theorem veluGlobalMorphism_kernel (P : E.toAffine.Point) (hP : P ∈ G) :
    (affineSmoothPoint E P ≫ (integralSmoothOpen E).ι) ≫ veluGlobalMorphism E G hodd =
      integralCurveZero (curve E G) := by
  cases P with
  | zero =>
    change (affineSmoothPoint E (0 : (E.map (algebraMap K K)).toAffine.Point) ≫ _) ≫ _ = _
    rw [affineSmoothPoint_zero]
    change (Spec.map (𝟙 (CommRingCat.of K)) ≫ integralCurveZero E) ≫ _ = _
    rw [Spec.map_id, Category.id_comp, veluGlobalMorphism_zero]
  | some u v hQ => exact veluGlobalMorphism_affineKernel E G hodd hQ hP

/-- Outside the original subgroup, the global morphism evaluates to the original Vélu sums. -/
@[reassoc] theorem veluGlobalMorphism_affineNonkernel {u v : K}
    (hP : E.toAffine.Nonsingular u v) (hPG : Affine.Point.some u v hP ∉ G) :
    (affineSmoothPoint E (.some u v hP) ≫ (integralSmoothOpen E).ι) ≫
        veluGlobalMorphism E G hodd =
      Spec.map (CommRingCat.ofHom (veluTargetPointChart E G hodd hP hPG).toRingHom) ≫
        integralCurveChart (curve E G) 2 := by
  rw [affineSmoothPoint_some]
  change (Spec.map (CommRingCat.ofHom (veluSourcePointChart E hP).toRingHom) ≫ _) ≫ _ = _
  rw [← veluAffinePointLift_source E G hP hPG, Category.assoc, veluGlobalMorphism_affine]
  exact veluAffineRegularMorphism_point E G hodd hP hPG

end WeierstrassCurve.Velu

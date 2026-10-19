/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluTranslatedInfinityRepresentative
public import FLT.FreyCurve.Serre.VeluAffineNonkernelOpen

/-!
# The original Vélu rational map is regular at every original geometric point

Kernel points lie in actual translated infinity neighborhoods. Together with
the affine nonkernel and infinity constructions this covers every original
field-valued point; a scheme cover and global gluing remain separate work.
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

/-- Every original affine kernel point belongs to the original rational map's domain. -/
theorem veluKernelPoint_mem_rationalDomain {u v : K} (hQ : E.toAffine.Nonsingular u v)
    (hQG : Affine.Point.some u v hQ ∈ G) (z : Spec (.of K)) :
    (affineSmoothPoint E (.some u v hQ) ≫ (integralSmoothOpen E).ι) z ∈
      (veluSchemeRationalMap E G hodd).domain := by
  have hn := (Affine.nonsingular_neg u v).mpr hQ
  have hm : Affine.Point.some u (E.toAffine.negY u v) hn ∈ G := G.neg_mem hQG
  have h := veluNegativeKernelPoint_mem_rationalDomain E G hodd hn hm z
  change (affineSmoothPoint E (-(-Affine.Point.some u v hQ)) ≫
    (integralSmoothOpen E).ι) z ∈ _ at h
  simpa only [neg_neg] using h

/-- Every original affine point lies in the original rational map's domain. -/
theorem veluAffinePoint_mem_rationalDomain {u v : K} (hQ : E.toAffine.Nonsingular u v)
    (z : Spec (.of K)) :
    (affineSmoothPoint E (.some u v hQ) ≫ (integralSmoothOpen E).ι) z ∈
      (veluSchemeRationalMap E G hodd).domain := by
  by_cases hQG : Affine.Point.some u v hQ ∈ G
  · exact veluKernelPoint_mem_rationalDomain E G hodd hQ hQG z
  · rw [affineSmoothPoint_some]
    exact veluAffineNonkernel_mem_rationalDomain E G hQ hodd hQG z

/-- Every original point of the affine group lies in the rational domain, including zero. -/
theorem veluOriginalPoint_mem_rationalDomain (P : E.toAffine.Point) (z : Spec (.of K)) :
    (affineSmoothPoint E P ≫ (integralSmoothOpen E).ι) z ∈
      (veluSchemeRationalMap E G hodd).domain := by
  cases P with
  | zero =>
    change (affineSmoothPoint E (0 : (E.map (algebraMap K K)).toAffine.Point) ≫ _) z ∈ _
    rw [affineSmoothPoint_zero]
    change (Spec.map (𝟙 (CommRingCat.of K)) ≫ integralCurveZero E) z ∈ _
    rw [Spec.map_id, Category.id_comp]
    exact veluInfinityPoint_mem_rationalDomain E G hodd z
  | some u v hQ => exact veluAffinePoint_mem_rationalDomain E G hodd hQ z

end WeierstrassCurve.Velu

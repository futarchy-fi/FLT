/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluAffineTranslation
public import FLT.FreyCurve.Serre.VeluInfinityRationalRepresentative

/-!
# Transporting the actual infinity neighborhood by original translations

Inverse translation embeds the existing regular neighborhood as an actual
open neighborhood of the original negative translating point.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] [CharZero K] [DecidableEq K]
  (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]

omit [CharZero K] in
/-- Scalar extension to the original field retains the original affine point. -/
theorem affineScalarPoint_self (P : E.toAffine.Point) :
    affineScalarPoint (L := K) E P = P := by
  cases P <;> rfl

/-- The actual source infinity morphism is the actual zero section. -/
theorem veluInfinityPointLift_zero :
    veluInfinityPointLift E G ≫ veluInfinityOpenImmersion E G = integralCurveZero E :=
  veluInfinityPointLift_source E G

omit [CharZero K] [DecidableEq K] in
/-- Inverse translation carries original infinity to the original negative point. -/
theorem affineTranslationIso_inverse_zero (P : E.toAffine.Point) :
    integralCurveZero E ≫ (affineTranslationIso E P).inv =
      affineSmoothPoint E (-P) ≫ (integralSmoothOpen E).ι := by
  classical
  have h := affineTranslationIso_action (L := K) E P (-P)
  rw [affineScalarPoint_self, add_neg_cancel, affineSmoothPoint_zero] at h
  change _ = Spec.map (𝟙 (CommRingCat.of K)) ≫ integralCurveZero E at h
  rw [Spec.map_id, Category.id_comp] at h
  rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The original infinity neighborhood transported by the actual inverse translation. -/
def veluTranslatedInfinityOpenImmersion (P : E.toAffine.Point) :
    Spec (.of (InfinityTargetRing E G)) ⟶ integralCurve E :=
  veluInfinityOpenImmersion E G ≫ (affineTranslationIso E P).inv

/-- The transported neighborhood is an actual open immersion of schemes. -/
instance veluTranslatedInfinityOpenImmersion_isOpenImmersion (P : E.toAffine.Point) :
    IsOpenImmersion (veluTranslatedInfinityOpenImmersion E G P) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ (affineTranslationIso E P).inv))

/-- Its original lifted infinity point is the actual original negative translating point. -/
@[reassoc] theorem veluTranslatedInfinityPoint_source (P : E.toAffine.Point) :
    veluInfinityPointLift E G ≫ veluTranslatedInfinityOpenImmersion E G P =
      affineSmoothPoint E (-P) ≫ (integralSmoothOpen E).ι := by
  rw [veluTranslatedInfinityOpenImmersion, ← Category.assoc, veluInfinityPointLift_zero,
    affineTranslationIso_inverse_zero]

/-- Every point of the original negative section lies in the transported open. -/
theorem veluTranslatedInfinityPoint_mem_open (P : E.toAffine.Point) (z : Spec (.of K)) :
    (affineSmoothPoint E (-P) ≫ (integralSmoothOpen E).ι) z ∈
      (veluTranslatedInfinityOpenImmersion E G P).opensRange := by
  rw [← veluTranslatedInfinityPoint_source E G P]
  exact ⟨veluInfinityPointLift E G z, rfl⟩

end WeierstrassCurve.Velu

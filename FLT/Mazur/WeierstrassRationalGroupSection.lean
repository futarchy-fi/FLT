/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassGeneralizedEllipticModel
public import FLT.Mazur.WeierstrassProjectiveGroupComparison
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Classical rational points in the generalized curve's actual group

The existing projective point comparison is precomposed with the identity-base
comparison. This gives actual group sections of the constructed generalized
curve, retains the original scheme point, and preserves its exact order.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj

namespace FLT.Mazur.WeierstrassIntegralChart

variable {K : Type} [Field K] (W : WeierstrassCurve K) (hΔ : IsUnit W.Δ)

/-- The scalar map from a field to itself is the identity base object. -/
def rationalSectionSourceIso : Over.mk (𝟙 (Spec (.of K))) ≅
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K K))) :=
  Over.isoMk (Iso.refl (Spec (.of K))) (by
    change 𝟙 _ ≫ Spec.map (𝟙 (CommRingCat.of K)) = 𝟙 _
    rw [Category.id_comp, Spec.map_id])

/-- The classical projective point as a section of the actual generalized curve group. -/
def projectiveRationalGroupSection
    (P : (W.map (algebraMap K K)).toProjective.Point) :
    Over.mk (𝟙 (Spec (.of K))) ⟶ (integralGeneralizedEllipticCurve W hΔ).group :=
  (rationalSectionSourceIso (K := K)).hom ≫ projectiveToIntegral W P

/-- The geometric section comparison is an additive group homomorphism. -/
def projectiveRationalGroupSectionAddHom :
    (W.map (algebraMap K K)).toProjective.Point →+
      Additive (Over.mk (𝟙 (Spec (.of K))) ⟶ (integralGeneralizedEllipticCurve W hΔ).group) := by
  let _ := integralCurveCommGrpObj W hΔ
  refine AddMonoidHom.mk' (fun P ↦ Additive.ofMul (projectiveRationalGroupSection W hΔ P)) ?_
  intro P Q
  change (rationalSectionSourceIso (K := K)).hom ≫ projectiveToIntegral W (P + Q) =
    ((rationalSectionSourceIso (K := K)).hom ≫ projectiveToIntegral W P) *
      ((rationalSectionSourceIso (K := K)).hom ≫ projectiveToIntegral W Q)
  rw [projectiveToIntegral_add W hΔ]
  exact MonObj.comp_mul _ _ _

/-- Distinct classical points give distinct sections of the genuine geometric group. -/
theorem projectiveRationalGroupSection_injective :
    Function.Injective (projectiveRationalGroupSection W hΔ) := by
  intro P Q h
  apply projectiveToIntegral_injective W
  exact (cancel_epi (rationalSectionSourceIso (K := K)).hom).mp h

/-- The original point's exact additive order is its actual group section's order. -/
theorem projectiveRationalGroupSection_order
    (P : (W.map (algebraMap K K)).toProjective.Point) :
    orderOf (projectiveRationalGroupSection W hΔ P) = addOrderOf P :=
  addOrderOf_injective (projectiveRationalGroupSectionAddHom W hΔ)
    (projectiveRationalGroupSection_injective W hΔ) P

end FLT.Mazur.WeierstrassIntegralChart

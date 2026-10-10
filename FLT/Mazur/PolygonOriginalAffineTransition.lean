/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOriginalAffineQuotient

/-!
# Original transitions on affine parameter quotients

Restriction along the original polygon transition is the usual quotient
factor map. This supplies compatibility of the actual affine quotient
comparisons, rather than choosing unrelated isomorphisms at each order.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] family exactVeroneseProj originalStageToCompatibleProj
  originalStageAffineQuotient

/-- Equality of scheme maps gives equality on fixed source and target opens. -/
theorem affineRestriction_congr {X Y : Scheme} {f g : X ⟶ Y} (e : f = g)
    (U : Y.Opens) (V : X.Opens) (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V hf = g.appLE U V hg := by
  subst g
  rfl

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Original transitions retain the inverse image of each complete affine open. -/
theorem originalStageAffineOpen_transition {a b : ℕ} (f : a ⟶ b)
    (U : (exactVeroneseProj K n h).affineOpens) :
    originalStageToCompatibleProj K n h a ⁻¹ᵁ U =
      (stageSystem K n h).map f ⁻¹ᵁ (originalStageToCompatibleProj K n h b ⁻¹ᵁ U) := by
  rw [← Scheme.Hom.comp_preimage, originalStageToCompatibleProj_naturality]

/-- The actual restriction of sections along an original stage transition. -/
def originalStageAffineTransition {a b : ℕ} (f : a ⟶ b)
    (U : (exactVeroneseProj K n h).affineOpens) :
    Γ((family K b n h).left, originalStageToCompatibleProj K n h b ⁻¹ᵁ U) →+*
      Γ((family K a n h).left, originalStageToCompatibleProj K n h a ⁻¹ᵁ U) :=
  (((stageSystem K n h).map f).appLE _ _
    (originalStageAffineOpen_transition K n h f U).le).hom

/-- Original stage restrictions commute with restriction from the complete family. -/
theorem originalStageAffineTransition_app {a b : ℕ} (f : a ⟶ b)
    (U : (exactVeroneseProj K n h).affineOpens) (s : Γ(exactVeroneseProj K n h, U)) :
    originalStageAffineTransition K n h f U
      ((originalStageToCompatibleProj K n h b).app U s) =
        (originalStageToCompatibleProj K n h a).app U s := by
  change (((originalStageToCompatibleProj K n h b).app U) ≫
    ((stageSystem K n h).map f).appLE _ _ _ ) s = _
  rw [← Scheme.Hom.comp_appLE]
  rw [affineRestriction_congr (originalStageToCompatibleProj_naturality K n h f)
    _ _ _ le_rfl]
  change ((originalStageToCompatibleProj K n h a).appLE U _ le_rfl) s = _
  simp only [Scheme.Hom.appLE, homOfLE_refl, CategoryTheory.op_id]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- The compatible quotient comparison uses the actual original polygon transitions. -/
theorem originalStageAffineQuotient_transition {a b : ℕ} (f : a ⟶ b)
    (U : (exactVeroneseProj K n h).affineOpens)
    (s : Γ(exactVeroneseProj K n h, U) ⧸
      (compatibleProjAdicIdeal K n h).ideal U ^ (b + 1)) :
    originalStageAffineTransition K n h f U (originalStageAffineQuotient K n h b U s) =
      originalStageAffineQuotient K n h a U
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right
          (Nat.add_le_add_right (leOfHom f) 1)) s) := by
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  rw [Ideal.Quotient.factor_mk, originalStageAffineQuotient_mk,
    originalStageAffineQuotient_mk, originalStageAffineTransition_app]

end FLT.Mazur.PolygonInfinitesimalStages

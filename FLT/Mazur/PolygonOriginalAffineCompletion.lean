/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOriginalAffineTransition
public import FLT.Mazur.PolygonOriginalAffineScalars
public import FLT.Mazur.AdicCompletionPositiveLimit

/-!
# Actual affine completion of the compatible polygon

The parameter-adic completion on an affine open of the complete candidate
is the ring of compatible sections on its original polygon stages.
The isomorphism retains every stage evaluation and every base coefficient.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] family exactVeroneseProj originalStageToCompatibleProj
  originalStageAffineQuotient originalStageAffineTransition

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (U : (exactVeroneseProj K n h).affineOpens)

/-- Compatible sections on the actual original stage opens, with their original maps. -/
def originalAffineFormalSections : Subring
    (∀ m : ℕ, Γ((family K m n h).left, originalStageToCompatibleProj K n h m ⁻¹ᵁ U)) where
  carrier := {s | ∀ {a b : ℕ} (f : a ⟶ b),
    originalStageAffineTransition K n h f U (s b) = s a}
  zero_mem' := by intro a b f; exact map_zero _
  one_mem' := by intro a b f; exact map_one _
  add_mem' := by intro x y hx hy a b f; simp only [Pi.add_apply, map_add, hx f, hy f]
  mul_mem' := by intro x y hx hy a b f; simp only [Pi.mul_apply, map_mul, hx f, hy f]
  neg_mem' := by intro x hx a b f; simp only [Pi.neg_apply, map_neg, hx f]

/-- The original affine quotient comparisons identify the two compatible section rings. -/
def originalAffineQuotientLimitEquiv :
    AdicCompletionPositiveLimit.sections ((compatibleProjAdicIdeal K n h).ideal U) ≃+*
      originalAffineFormalSections K n h U where
  toFun s := ⟨fun m ↦ originalStageAffineQuotient K n h m U (s.val m), by
    intro a b f
    rw [originalStageAffineQuotient_transition, s.property (leOfHom f)]⟩
  invFun s := ⟨fun m ↦ (originalStageAffineQuotient K n h m U).symm (s.val m), by
    intro a b hab
    apply (originalStageAffineQuotient K n h a U).injective
    rw [← originalStageAffineQuotient_transition K n h (homOfLE hab),
      RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    exact s.property (homOfLE hab)⟩
  left_inv s := by
    apply Subtype.ext
    funext m
    exact (originalStageAffineQuotient K n h m U).symm_apply_apply (s.val m)
  right_inv s := by
    apply Subtype.ext
    funext m
    exact (originalStageAffineQuotient K n h m U).apply_symm_apply (s.val m)
  map_mul' x y := by
    apply Subtype.ext
    funext m
    exact map_mul (originalStageAffineQuotient K n h m U) (x.val m) (y.val m)
  map_add' x y := by
    apply Subtype.ext
    funext m
    exact map_add (originalStageAffineQuotient K n h m U) (x.val m) (y.val m)

/-- The actual complete affine ring completed along its original parameter ideal. -/
def originalAffineCompletionEquiv :
    AdicCompletion ((compatibleProjAdicIdeal K n h).ideal U)
      Γ(exactVeroneseProj K n h, U) ≃+* originalAffineFormalSections K n h U :=
  (AdicCompletionPositiveLimit.equivalence _).trans
    (originalAffineQuotientLimitEquiv K n h U)

/-- Completion comparison retains each original-stage evaluation exactly. -/
theorem originalAffineCompletionEquiv_eval (m : ℕ)
    (s : AdicCompletion ((compatibleProjAdicIdeal K n h).ideal U)
      Γ(exactVeroneseProj K n h, U)) :
    (originalAffineCompletionEquiv K n h U s).val m =
      originalStageAffineQuotient K n h m U
        (AdicCompletion.evalₐ ((compatibleProjAdicIdeal K n h).ideal U) (m + 1) s) := rfl

/-- Actual affine sections restrict to their original sections at every finite stage. -/
theorem originalAffineCompletionEquiv_of (m : ℕ) (s : Γ(exactVeroneseProj K n h, U)) :
    (originalAffineCompletionEquiv K n h U
      (AdicCompletion.of ((compatibleProjAdicIdeal K n h).ideal U) _ s)).val m =
        (originalStageToCompatibleProj K n h m).app U s := by
  rw [originalAffineCompletionEquiv_eval, AdicCompletion.evalₐ_of,
    originalStageAffineQuotient_mk]

/-- All original complete-base coefficients, in particular q, survive the comparison. -/
theorem originalAffineCompletionEquiv_scalars (m : ℕ) (r : PowerSeries K) :
    (originalAffineCompletionEquiv K n h U
      (AdicCompletion.of ((compatibleProjAdicIdeal K n h).ideal U) _
        (completeAffineScalars K n h U r))).val m = originalStageAffineScalars K n h m U r := by
  rw [originalAffineCompletionEquiv_of, originalStage_app_scalars]

end FLT.Mazur.PolygonInfinitesimalStages

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstGraphBranchExt

/-!
# Closed equations on both punctures extend to the full finite graph

The two punctures are schematically dense in the finite graph. A morphism
whose two restrictions factor through a closed immersion therefore factors
through that same full closed subscheme, with all nilpotents retained.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "S" => Ring K[T;T⁻¹] 1
local notation "L" => (S)[T;T⁻¹]
local notation "E" => completeIdentityFirstGraphScheme K n h i
local notation "t" => completeIdentityFirstGraphBothBranches K n h i
local notation "l" => completeIdentityFirstGraphLeftBranch K n h i
local notation "r" => completeIdentityFirstGraphRightBranch K n h i
variable {X Y : Scheme} (e : X ⟶ Y) [IsClosedImmersion e]
  (f : completeIdentityFirstGraphScheme K n h i ⟶ Y)
  (a b : PolygonSmoothing.branchTorus (Ring K[T;T⁻¹] 1) ⟶ X)
  (ha : a ≫ e = completeIdentityFirstGraphLeftBranch K n h i ≫ f)
  (hb : b ≫ e = completeIdentityFirstGraphRightBranch K n h i ≫ f)

include ha hb in
/-- The full finite graph satisfies every closed equation satisfied on its two punctures. -/
theorem completeIdentityFirstGraph_closedPullback_isIso : IsIso (pullback.snd e f) := by
  let g : Spec (.of ((L) × (L))) ⟶ X :=
    inv (coprodSpec (L) (L)) ≫ coprod.desc a b
  have hg : g ≫ e = (t) ≫ f := by
    apply (cancel_epi (coprodSpec (L) (L))).mp
    dsimp only [g]
    rw [← Category.assoc, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
    apply coprod.hom_ext
    · simpa only [Category.assoc, coprod.inl_desc_assoc, coprodSpec_inl_assoc,
        completeIdentityFirstGraphBothBranches_left_assoc] using ha
    · simpa only [Category.assoc, coprod.inr_desc_assoc, coprodSpec_inr_assoc,
        completeIdentityFirstGraphBothBranches_right_assoc] using hb
  let u : Spec (.of ((L) × (L))) ⟶ pullback e f := pullback.lift g (t) hg
  apply IsClosedImmersion.isIso_iff_ker_eq_bot.mpr
  apply le_bot_iff.mp
  have he := u.le_ker_comp (pullback.snd e f)
  simpa only [u, pullback.lift_snd, Scheme.Hom.ker_eq_bot] using he

/-- The constructed factorization through the original full closed subscheme. -/
def completeIdentityFirstGraphClosedLift : (E) ⟶ X :=
  let _ := completeIdentityFirstGraph_closedPullback_isIso K n h i e f a b ha hb
  inv (pullback.snd e f) ≫ pullback.fst e f

/-- The factorization retains the original whole-graph morphism exactly. -/
@[reassoc] theorem completeIdentityFirstGraphClosedLift_fac :
    completeIdentityFirstGraphClosedLift K n h i e f a b ha hb ≫ e = f := by
  let _ := completeIdentityFirstGraph_closedPullback_isIso K n h i e f a b ha hb
  rw [completeIdentityFirstGraphClosedLift, Category.assoc, pullback.condition,
    IsIso.inv_hom_id_assoc]

end FLT.Mazur.PolygonInfinitesimalStages

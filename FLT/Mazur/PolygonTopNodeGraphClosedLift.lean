/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonTopNodeGraphBranchExt

/-!
# Closed equations on both punctures extend to the full higher graph

The two punctures are schematically dense in the higher graph. A morphism
whose two restrictions factor through a closed immersion therefore factors
through that same full closed subscheme, with all nilpotents retained.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (R : Type) [CommRing R] (m : ℕ)
variable (u v : ((Ring R (m + 1))[T;T⁻¹])ˣ)
local notation "S" => Ring R (m + 1)
local notation "L" => (S)[T;T⁻¹]
local notation "E" => topNodeGraphScheme R m u v
local notation "t" => topNodeGraphBranches R m u v
local notation "l" => topNodeGraphLeftBranch R m u v
local notation "r" => topNodeGraphRightBranch R m u v
variable {X Y : Scheme} (e : X ⟶ Y) [IsClosedImmersion e]
  (f : topNodeGraphScheme R m u v ⟶ Y)
  (a b : PolygonSmoothing.branchTorus (Ring R (m + 1)) ⟶ X)
  (ha : a ≫ e = topNodeGraphLeftBranch R m u v ≫ f)
  (hb : b ≫ e = topNodeGraphRightBranch R m u v ≫ f)

include ha hb in
/-- The full higher graph satisfies every closed equation satisfied on its two punctures. -/
theorem topNodeGraph_closedPullback_isIso : IsIso (pullback.snd e f) := by
  let g : Spec (.of ((L) × (L))) ⟶ X :=
    inv (coprodSpec (L) (L)) ≫ coprod.desc a b
  have hg : g ≫ e = (t) ≫ f := by
    apply (cancel_epi (coprodSpec (L) (L))).mp
    dsimp only [g]
    rw [← Category.assoc, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
    apply coprod.hom_ext
    · simpa only [Category.assoc, coprod.inl_desc_assoc, coprodSpec_inl_assoc,
        topNodeGraphBranches_left_assoc] using ha
    · simpa only [Category.assoc, coprod.inr_desc_assoc, coprodSpec_inr_assoc,
        topNodeGraphBranches_right_assoc] using hb
  let liftMap : Spec (.of ((L) × (L))) ⟶ pullback e f := pullback.lift g (t) hg
  apply IsClosedImmersion.isIso_iff_ker_eq_bot.mpr
  apply le_bot_iff.mp
  have he := liftMap.le_ker_comp (pullback.snd e f)
  simpa only [liftMap, pullback.lift_snd, Scheme.Hom.ker_eq_bot] using he

/-- The constructed factorization through the original full closed subscheme. -/
def topNodeGraphClosedLift : (E) ⟶ X :=
  let _ := topNodeGraph_closedPullback_isIso R m u v e f a b ha hb
  inv (pullback.snd e f) ≫ pullback.fst e f

/-- The factorization retains the original whole-graph morphism exactly. -/
@[reassoc] theorem topNodeGraphClosedLift_fac :
    topNodeGraphClosedLift R m u v e f a b ha hb ≫ e = f := by
  let _ := topNodeGraph_closedPullback_isIso R m u v e f a b ha hb
  rw [topNodeGraphClosedLift, Category.assoc, pullback.condition,
    IsIso.inv_hom_id_assoc]

end FLT.Mazur.PolygonInfinitesimalStages

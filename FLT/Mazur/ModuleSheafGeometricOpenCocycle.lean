/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafOpenOverlapTransition
public import FLT.Mazur.ModuleSheafImageChartGluing

/-!
# Section cocycles from geometric transitions on common opens

Chart isomorphisms on all common subopens, with their proved pullback coherence
and cocycle, give the actual section cocycle for the original chart pushforwards.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.ModuleSheafGluing
open ModuleSheafOpenImageChart ModuleSheafOpenOverlapTransition
open ModuleSheafMorphismGluing SheafPullbackPathComparison
universe u
attribute [local irreducible] Scheme.Modules.pullback Scheme.Modules.pushforward
variable {X : Scheme.{u}} {ι : Type u} (Y : ι → Scheme.{u})
  (i : ∀ j, Y j ⟶ X) [∀ j, IsOpenImmersion (i j)] (M : ∀ j, (Y j).Modules)
variable (e : ∀ j k (U : X.Opens) (hj : U ≤ (i j).opensRange) (hk : U ≤ (i k).opensRange),
  (pullback (coordinate (i j) U hj)).obj (M j) ≅
    (pullback (coordinate (i k) U hk)).obj (M k))

/-- Geometric transitions on the entire pair intersections, as ambient local isomorphisms. -/
@[irreducible] def geometricTransition (j k : ι) :
    ((pushforward (i j)).obj (M j)).over ((i j).opensRange ⊓ (i k).opensRange) ≅
      ((pushforward (i k)).obj (M k)).over ((i j).opensRange ⊓ (i k).opensRange) :=
  transition (i j) (i k) _ inf_le_left inf_le_right (e j k _ inf_le_left inf_le_right)

variable (hr : ∀ j k (U V : X.Opens) (h : V ≤ U)
  (hj : U ≤ (i j).opensRange) (hk : U ≤ (i k).opensRange),
  (pullback (X.homOfLE h)).map (e j k U hj hk).hom ≫
      (comparison (X.homOfLE h) (coordinate (i k) U hk)
        (coordinate (i k) V (h.trans hk)) (coordinate_refine (i k) h hk)).hom.app (M k) =
    (comparison (X.homOfLE h) (coordinate (i j) U hj)
        (coordinate (i j) V (h.trans hj)) (coordinate_refine (i j) h hj)).hom.app (M j) ≫
      (e j k V (h.trans hj) (h.trans hk)).hom)
variable (hc : ∀ j k l (U : X.Opens) (hj : U ≤ (i j).opensRange)
  (hk : U ≤ (i k).opensRange) (hl : U ≤ (i l).opensRange),
  (e j k U hj hk).hom ≫ (e k l U hk hl).hom = (e j l U hj hl).hom)

include hr in
/-- Each pair transition restricts to its independently constructed subopen comparison. -/
theorem geometricTransition_app (j k : ι) (V : X.Opens)
    (hj : V ≤ (i j).opensRange) (hk : V ≤ (i k).opensRange) :
    localApp (geometricTransition Y i M e j k).hom (le_inf hj hk) =
      localApp (transition (i j) (i k) V hj hk (e j k V hj hk)).hom le_rfl := by
  unfold geometricTransition
  exact (transition_refine_app (i j) (i k) _ inf_le_left inf_le_right
    (e j k _ inf_le_left inf_le_right) V (le_inf hj hk) (e j k V hj hk)
    (hr j k _ V (le_inf hj hk) inf_le_left inf_le_right) V le_rfl).symm

include hr hc in
/-- The actual geometric cocycle is the sectionwise cocycle consumed by sheaf gluing. -/
theorem geometricTransition_cocycle (j k l : ι) (V : X.Opens)
    (hj : V ≤ (i j).opensRange) (hk : V ≤ (i k).opensRange)
    (hl : V ≤ (i l).opensRange) (s : Γ((pushforward (i j)).obj (M j), V)) :
    localApp (geometricTransition Y i M e k l).hom (le_inf hk hl)
        (localApp (geometricTransition Y i M e j k).hom (le_inf hj hk) s) =
      localApp (geometricTransition Y i M e j l).hom (le_inf hj hl) s := by
  rw [geometricTransition_app Y i M e hr, geometricTransition_app Y i M e hr,
    geometricTransition_app Y i M e hr]
  exact transition_cocycle_app (i j) (i k) V hj hk (e j k V hj hk) (i l) hl
    (e k l V hk hl) (e j l V hj hl) (hc j k l V hj hk hl) V le_rfl s

include hr hc in
/-- The geometric cocycle in the sealed evaluator used for concrete chart pushforwards. -/
theorem geometricTransition_cocycle_eval (j k l : ι) (V : X.Opens)
    (hj : V ≤ (i j).opensRange) (hk : V ≤ (i k).opensRange)
    (hl : V ≤ (i l).opensRange) (s : Γ((pushforward (i j)).obj (M j), V)) :
    localEval (geometricTransition Y i M e k l).hom (le_inf hk hl)
        (localEval (geometricTransition Y i M e j k).hom (le_inf hj hk) s) =
      localEval (geometricTransition Y i M e j l).hom (le_inf hj hl) s := by
  simpa only [localEval] using geometricTransition_cocycle Y i M e hr hc j k l V hj hk hl s

end FLT.Mazur.ModuleSheafGluing

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossRefinementBaseSquare
public import FLT.Mazur.SchemeAffineOpenOverlapCover

/-!
# Effective comparisons on arbitrary affine charts of the base overlap

Each affine map to the geometric overlap has its own constructed common cover.
Refining this affine map preserves the effective comparison, even when neither
of the two independently chosen covering maps factors through the old cover.
-/

open Lean Meta Elab Tactic

-- Keep implicit type arguments separate even when they are definitionally equal.
-- Fixing them during congruence makes the kernel unfold large pullback constructions.
private meta partial def structuralCongr (g : MVarId) (fuel : Nat) : MetaM (List MVarId) :=
  g.withContext do
    let t ← instantiateMVars (← g.getType)
    let sides : Option (Expr × Expr) := match t.eq? with
      | some (_, a, b) => some (a, b)
      | none => t.heq?.map fun (_, a, _, b) => (a, b)
    let some (a, b) := sides | return [g]
    if a == b then
      try g.refl; return [] catch _ =>
        try g.hrefl; return [] catch _ => return [g]
    if fuel == 0 then return [g]
    if a.getAppFn == b.getAppFn && a.getAppNumArgs == b.getAppNumArgs && a.isApp then
      if let some gs ← g.hcongr? then
        return (← gs.mapM fun h => structuralCongr h (fuel - 1)).flatten
    return [g]
local elab "structural_hcongr" : tactic => liftMetaTactic fun g => structuralCongr g 12

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] commonCoverRing commonCoverMap
  CrossRefinement.effectiveComparison AffineRefinementPullback.compositionChart
variable {X Y : Scheme.{u}} {p : Y ⟶ X} (C C' : Chart p)
variable {A B : CommRingCat.{u}} (f : Spec A ⟶ C.baseOverlap C')

/-- Construct the common cover for any affine chart of the geometric overlap. -/
def overlapChartCrossRefinement : C.CrossRefinement C' :=
  C.commonBaseCrossRefinement C'
    (Spec.preimage (f ≫ Limits.pullback.fst C.base C'.base))
    (Spec.preimage (f ≫ Limits.pullback.snd C.base C'.base)) (by
      simp only [Spec.map_preimage, Category.assoc, Limits.pullback.condition])

/-- The standard overlap cover is a special case of the arbitrary-chart construction. -/
theorem overlapChartCrossRefinement_cover (i : (C.baseOverlapCover C').I₀) :
    C.overlapChartCrossRefinement C' ((C.baseOverlapCover C').f i) =
      C.overlapCrossRefinement C' i := rfl

variable (g : Spec B ⟶ C.baseOverlap C') (α : A ⟶ B) (w : Spec.map α ≫ f = g)

include w in
/-- Refinement of overlap charts refines the first base coordinate. -/
theorem overlapChartCrossRefinement_leftBase :
    (C.overlapChartCrossRefinement C' f).leftBase ≫ α =
      (C.overlapChartCrossRefinement C' g).leftBase := by
  apply Spec.map_injective
  simp only [overlapChartCrossRefinement, commonBaseCrossRefinement,
    Spec.map_comp, Spec.map_preimage, ← Category.assoc, w]

include w in
/-- Refinement of overlap charts refines the second base coordinate independently. -/
theorem overlapChartCrossRefinement_rightBase :
    (C.overlapChartCrossRefinement C' f).rightBase ≫ α =
      (C.overlapChartCrossRefinement C' g).rightBase := by
  apply Spec.map_injective
  simp only [overlapChartCrossRefinement, commonBaseCrossRefinement,
    Spec.map_comp, Spec.map_preimage, ← Category.assoc, w]

attribute [local irreducible] CrossRefinement.leftChart CrossRefinement.rightChart
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [((pullback C.cover).obj M).IsQuasicoherent]
variable [((pullback C'.cover).obj M).IsQuasicoherent]

/-- Comparison on a refined affine overlap chart is the restricted original comparison. -/
theorem overlapChart_effectiveComparison_restrict :
    (pullback (Spec.map α)).map
        ((C.overlapChartCrossRefinement C' f).effectiveComparison D).hom ≫
        (AffineRefinementPullback.compositionChart
          (C.overlapChartCrossRefinement C' f).rightBase α (C'.sheaf D)).hom ≫
        (pullbackCongr (congrArg Spec.map
          (C.overlapChartCrossRefinement_rightBase C' f g α w))).hom.app (C'.sheaf D) =
      (AffineRefinementPullback.compositionChart
          (C.overlapChartCrossRefinement C' f).leftBase α (C.sheaf D)).hom ≫
        (pullbackCongr (congrArg Spec.map
          (C.overlapChartCrossRefinement_leftBase C' f g α w))).hom.app (C.sheaf D) ≫
        ((C.overlapChartCrossRefinement C' g).effectiveComparison D).hom := by
  have h := (C.overlapChartCrossRefinement C' f).effectiveComparison_base_square
    (C.overlapChartCrossRefinement C' g) D α
    (C.overlapChartCrossRefinement_leftBase C' f g α w)
    (C.overlapChartCrossRefinement_rightBase C' f g α w)
  refine eq_of_heq (HEq.trans ?_ (HEq.trans (heq_of_eq h) ?_))
  all_goals
    structural_hcongr <;> first
    | rfl
    | exact C.overlapChartCrossRefinement_leftBase C' f g α w
    | exact C.overlapChartCrossRefinement_rightBase C' f g α w

end FLT.Mazur.SchemeAffineDescent.Chart

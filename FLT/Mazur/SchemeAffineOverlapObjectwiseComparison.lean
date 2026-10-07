/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffinePullbackNormalizedSquare
public import FLT.Mazur.SchemeAffineOverlapChartComparison

/-!
# Objectwise normalization of affine overlap restriction

The independent comparison square is expressed with the geometric composite
pullback isomorphisms used by local sheaf-map refinement.
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
open FLT.Mazur.AffineIteratedPullbackSections
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] CrossRefinement.effectiveComparison
  CrossRefinement.leftChart CrossRefinement.rightChart commonCoverRing commonCoverMap
  AffineRefinementPullback.compositionChart compositeIso
variable {X Y : Scheme.{u}} {p : Y ⟶ X} (C C' : Chart p)
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [((pullback C.cover).obj M).IsQuasicoherent]
variable [((pullback C'.cover).obj M).IsQuasicoherent]
namespace CrossRefinement
variable {C C'} (ρ σ : C.CrossRefinement C')

/-- Independent cross refinements satisfy the normalized geometric square. -/
theorem effectiveComparison_base_objectwise_square (α : ρ.baseRing ⟶ σ.baseRing)
    (hl : ρ.leftBase ≫ α = σ.leftBase) (hr : ρ.rightBase ≫ α = σ.rightBase) :
    (pullback (Spec.map α)).map (ρ.effectiveComparison D).hom ≫
        (compositeIso (Spec.map α) (Spec.map ρ.rightBase) (Spec.map σ.rightBase)
          ((Spec.map_comp _ α).symm.trans (congrArg Spec.map hr)) (C'.sheaf D)).hom =
      (compositeIso (Spec.map α) (Spec.map ρ.leftBase) (Spec.map σ.leftBase)
          ((Spec.map_comp _ α).symm.trans (congrArg Spec.map hl)) (C.sheaf D)).hom ≫
        (σ.effectiveComparison D).hom :=
  affine_square_normalized ρ.leftBase ρ.rightBase α σ.leftBase σ.rightBase hl hr
    (C.sheaf D) (C'.sheaf D) (ρ.effectiveComparison D).hom (σ.effectiveComparison D).hom
    (ρ.effectiveComparison_base_square σ D α hl hr)

end CrossRefinement

variable {A B : CommRingCat.{u}} (f : Spec A ⟶ C.baseOverlap C')
variable (g : Spec B ⟶ C.baseOverlap C') (α : A ⟶ B) (w : Spec.map α ≫ f = g)

/-- Affine restriction in the objectwise geometric normalization. -/
theorem overlapChart_effectiveComparison_objectwise :
    (pullback (Spec.map α)).map
        ((C.overlapChartCrossRefinement C' f).effectiveComparison D).hom ≫
        (compositeIso (Spec.map α)
          (Spec.map (C.overlapChartCrossRefinement C' f).rightBase)
          (Spec.map (C.overlapChartCrossRefinement C' g).rightBase)
          ((Spec.map_comp _ α).symm.trans (congrArg Spec.map
            (C.overlapChartCrossRefinement_rightBase C' f g α w))) (C'.sheaf D)).hom =
      (compositeIso (Spec.map α)
          (Spec.map (C.overlapChartCrossRefinement C' f).leftBase)
          (Spec.map (C.overlapChartCrossRefinement C' g).leftBase)
          ((Spec.map_comp _ α).symm.trans (congrArg Spec.map
            (C.overlapChartCrossRefinement_leftBase C' f g α w))) (C.sheaf D)).hom ≫
        ((C.overlapChartCrossRefinement C' g).effectiveComparison D).hom := by
  have h := (C.overlapChartCrossRefinement C' f).effectiveComparison_base_objectwise_square
    D (C.overlapChartCrossRefinement C' g) α
    (C.overlapChartCrossRefinement_leftBase C' f g α w)
    (C.overlapChartCrossRefinement_rightBase C' f g α w)
  refine eq_of_heq (HEq.trans ?_ (HEq.trans (heq_of_eq h) ?_))
  all_goals
    structural_hcongr <;> first
    | rfl
    | exact Spec.map (C.overlapChartCrossRefinement C' g).rightBase
    | exact Spec.map (C.overlapChartCrossRefinement C' g).leftBase
    | exact (Spec.map_comp _ α).symm.trans (congrArg Spec.map
        (C.overlapChartCrossRefinement_rightBase C' f g α w))
    | exact (Spec.map_comp _ α).symm.trans (congrArg Spec.map
        (C.overlapChartCrossRefinement_leftBase C' f g α w))

end FLT.Mazur.SchemeAffineDescent.Chart

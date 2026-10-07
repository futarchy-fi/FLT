/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineOverlapChartComparison

/-!
# Common affine refinements of independently chosen overlap charts

Take an affine open cover of the actual fiber product of two overlap charts.
Its members refine both charts and cover their intersection, without assuming
that this intersection is affine. The two effective comparisons agree there.
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
attribute [local irreducible] CrossRefinement.effectiveComparison
  AffineRefinementPullback.compositionChart
variable {X Y : Scheme.{u}} {p : Y ⟶ X} (C C' : Chart p)
variable {A B : CommRingCat.{u}}
variable (f : Spec A ⟶ C.baseOverlap C') (g : Spec B ⟶ C.baseOverlap C')

/-- Affine charts covering the geometric intersection of two independent overlap charts. -/
def overlapChartCommonCover : (Limits.pullback f g).AffineOpenCover :=
  (Limits.pullback f g).affineOpenCover

variable (i : (C.overlapChartCommonCover C' f g).I₀)

/-- Coordinates of the common refinement in the first overlap chart. -/
def overlapChartCommonLeft : A ⟶ (C.overlapChartCommonCover C' f g).X i :=
  Spec.preimage ((C.overlapChartCommonCover C' f g).f i ≫ Limits.pullback.fst f g)

/-- Coordinates of the common refinement in the second overlap chart. -/
def overlapChartCommonRight : B ⟶ (C.overlapChartCommonCover C' f g).X i :=
  Spec.preimage ((C.overlapChartCommonCover C' f g).f i ≫ Limits.pullback.snd f g)

/-- The common affine chart mapped into the original geometric overlap. -/
def overlapChartCommonMap :
    Spec ((C.overlapChartCommonCover C' f g).X i) ⟶ C.baseOverlap C' :=
  (C.overlapChartCommonCover C' f g).f i ≫ Limits.pullback.fst f g ≫ f

/-- The first triangle into the geometric overlap commutes. -/
theorem overlapChartCommonLeft_over :
    Spec.map (C.overlapChartCommonLeft C' f g i) ≫ f =
      C.overlapChartCommonMap C' f g i := by
  simp only [overlapChartCommonLeft, overlapChartCommonMap, Spec.map_preimage,
    Category.assoc]

/-- The independent second triangle has the same map into the overlap. -/
theorem overlapChartCommonRight_over :
    Spec.map (C.overlapChartCommonRight C' f g i) ≫ g =
      C.overlapChartCommonMap C' f g i := by
  simp only [overlapChartCommonRight, overlapChartCommonMap, Spec.map_preimage,
    Category.assoc, Limits.pullback.condition]

/-- The common refinement charts cover the entire intersection of the two charts. -/
theorem overlapChartCommonCover_covers (x : (Limits.pullback f g : Scheme.{u})) :
    ∃ i, x ∈ Set.range ((C.overlapChartCommonCover C' f g).f i) :=
  ⟨(C.overlapChartCommonCover C' f g).idx x,
    (C.overlapChartCommonCover C' f g).covers x⟩

/-- For open overlap charts, common refinement remains open in the first chart. -/
instance overlapChartCommonLeft_isOpenImmersion [IsOpenImmersion g] :
    IsOpenImmersion (Spec.map (C.overlapChartCommonLeft C' f g i)) := by
  dsimp only [overlapChartCommonLeft]
  rw [Spec.map_preimage]
  infer_instance

/-- For open overlap charts, common refinement remains open in the second chart. -/
instance overlapChartCommonRight_isOpenImmersion [IsOpenImmersion f] :
    IsOpenImmersion (Spec.map (C.overlapChartCommonRight C' f g i)) := by
  dsimp only [overlapChartCommonRight]
  rw [Spec.map_preimage]
  infer_instance

variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [((pullback C.cover).obj M).IsQuasicoherent]
variable [((pullback C'.cover).obj M).IsQuasicoherent]

/-- The two independently chosen chart comparisons agree on each common affine refinement. -/
theorem overlapChart_effectiveComparison_common :
    HEq
      ((AffineRefinementPullback.compositionChart
          (C.overlapChartCrossRefinement C' f).leftBase
          (C.overlapChartCommonLeft C' f g i) (C.sheaf D)).inv ≫
        (pullback (Spec.map (C.overlapChartCommonLeft C' f g i))).map
          ((C.overlapChartCrossRefinement C' f).effectiveComparison D).hom ≫
        (AffineRefinementPullback.compositionChart
          (C.overlapChartCrossRefinement C' f).rightBase
          (C.overlapChartCommonLeft C' f g i) (C'.sheaf D)).hom)
      ((AffineRefinementPullback.compositionChart
          (C.overlapChartCrossRefinement C' g).leftBase
          (C.overlapChartCommonRight C' f g i) (C.sheaf D)).inv ≫
        (pullback (Spec.map (C.overlapChartCommonRight C' f g i))).map
          ((C.overlapChartCrossRefinement C' g).effectiveComparison D).hom ≫
        (AffineRefinementPullback.compositionChart
          (C.overlapChartCrossRefinement C' g).rightBase
          (C.overlapChartCommonRight C' f g i) (C'.sheaf D)).hom) := by
  let h := C.overlapChartCommonMap C' f g i
  have hl := (C.overlapChartCrossRefinement C' f).effectiveComparison_base_choice_independent
    (C.overlapChartCrossRefinement C' h) D (C.overlapChartCommonLeft C' f g i)
    (C.overlapChartCrossRefinement_leftBase C' f h _
      (C.overlapChartCommonLeft_over C' f g i))
    (C.overlapChartCrossRefinement_rightBase C' f h _
      (C.overlapChartCommonLeft_over C' f g i))
  have hr := (C.overlapChartCrossRefinement C' g).effectiveComparison_base_choice_independent
    (C.overlapChartCrossRefinement C' h) D (C.overlapChartCommonRight C' f g i)
    (C.overlapChartCrossRefinement_leftBase C' g h _
      (C.overlapChartCommonRight_over C' f g i))
    (C.overlapChartCrossRefinement_rightBase C' g h _
      (C.overlapChartCommonRight_over C' f g i))
  have hh := hl.trans hr.symm
  refine HEq.trans ?_ (HEq.trans hh ?_)
  all_goals structural_hcongr <;> rfl

end FLT.Mazur.SchemeAffineDescent.Chart

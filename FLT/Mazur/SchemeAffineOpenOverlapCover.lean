/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCommonBaseCover

/-!
# Constructing affine covers on geometric chart overlaps

Choose the standard affine open cover of the fiber product of the base charts.
Every member has a constructed faithfully flat common cover of the two original
charts. No affine-intersection or separation assumption on the base is needed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} (C C' : Chart p)

/-- The actual geometric intersection, expressed without assuming it is affine. -/
abbrev baseOverlap : Scheme.{u} := pullback C.base C'.base

/-- Affine open charts covering the entire geometric base overlap. -/
def baseOverlapCover : (C.baseOverlap C').AffineOpenCover :=
  (C.baseOverlap C').affineOpenCover

variable (i : (C.baseOverlapCover C').I₀)

/-- Coordinate map from the first base chart to an affine overlap member. -/
def overlapLeftBase : C.baseRing ⟶ (C.baseOverlapCover C').X i :=
  Spec.preimage ((C.baseOverlapCover C').f i ≫ pullback.fst C.base C'.base)

/-- Coordinate map from the second base chart to the same affine overlap member. -/
def overlapRightBase : C'.baseRing ⟶ (C.baseOverlapCover C').X i :=
  Spec.preimage ((C.baseOverlapCover C').f i ≫ pullback.snd C.base C'.base)

/-- The overlap coordinates have the same image in the original base scheme. -/
theorem overlapBase_over :
    Spec.map (C.overlapLeftBase C' i) ≫ C.base =
      Spec.map (C.overlapRightBase C' i) ≫ C'.base := by
  simp only [overlapLeftBase, overlapRightBase, Spec.map_preimage, Category.assoc,
    pullback.condition]

/-- A faithfully flat common cover constructed on every affine open overlap member. -/
def overlapCrossRefinement : C.CrossRefinement C' :=
  C.commonBaseCrossRefinement C' (C.overlapLeftBase C' i) (C.overlapRightBase C' i)
    (C.overlapBase_over C' i)

/-- The chosen affine charts really cover every point of the geometric overlap. -/
theorem baseOverlapCover_covers (x : C.baseOverlap C') :
    ∃ i, x ∈ Set.range ((C.baseOverlapCover C').f i) :=
  ⟨(C.baseOverlapCover C').idx x, (C.baseOverlapCover C').covers x⟩

/-- For open base charts, each overlap member maps by an open immersion to the first chart. -/
instance overlapLeftBase_isOpenImmersion [IsOpenImmersion C'.base] :
    IsOpenImmersion (Spec.map (C.overlapLeftBase C' i)) := by
  dsimp only [overlapLeftBase]
  rw [Spec.map_preimage]
  infer_instance

/-- For open base charts, each overlap member maps by an open immersion to the second chart. -/
instance overlapRightBase_isOpenImmersion [IsOpenImmersion C.base] :
    IsOpenImmersion (Spec.map (C.overlapRightBase C' i)) := by
  dsimp only [overlapRightBase]
  rw [Spec.map_preimage]
  infer_instance

end FLT.Mazur.SchemeAffineDescent.Chart

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCyclicBoundaryStandardTranslation
public import FLT.Mazur.PolygonCyclicBoundaryFieldIncidence

/-!
# Normalization and nodes on the chosen standard boundary polygon

The specified coefficient isomorphisms retain the entire translated components
and nodes of the independently chosen standard polygon. Both comparisons use
the actual cyclic parameter and commute with the same finite relabeling.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonCyclicBoundary
open PolygonPinching PolygonUniversalAction CyclicBoundaryParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (m : ℕ) [NeZero m] (hm : 0 < m) (n : ℕ) [NeZero n]
  (f : Over.mk (ProjectiveLineProductCharts.parameterToBase K L) ⟶
    CyclicBoundaryParameter.parameter (G K m) n)
  (j : Multiplicative (ZMod n)) (k : Fin m)
local notation "p" => PolygonAtlas.normalization K m
local notation "q" => PolygonAtlas.nodes K m
local notation "h" => PolygonAtlas.isPushout K m hm
local notation "e" => PolygonStandardFieldExtension.iso K L m hm

/-- The translated complete component on the independently chosen standard polygon. -/
def standardComponent : component L ⟶ PolygonAtlas.polygon L m :=
  componentι L m k ≫ PolygonAtlas.normalization L m ≫
    (standardTranslationIso K L m hm n f j).hom

/-- The translated original node on the independently chosen standard polygon. -/
def standardNode : point L ⟶ PolygonAtlas.polygon L m :=
  nodeι L m k ≫ PolygonAtlas.nodes L m ≫ (standardTranslationIso K L m hm n f j).hom

/-- The specified projective-line comparison retains each entire translated component. -/
@[reassoc] theorem standardComponent_comparison :
    standardComponent K L m hm n f j k ≫ (e).hom =
      (ProjectiveLineFieldExtension.componentIso K L).hom ≫
        extendedComponent K L m hm (p) (q) (h) n f j k := by
  rw [standardComponent, Category.assoc, Category.assoc, standardTranslation_comparison,
    PolygonStandardFieldExtension.component_iso_assoc]
  rfl

/-- The specified point comparison retains every translated original node. -/
@[reassoc] theorem standardNode_comparison :
    standardNode K L m hm n f j k ≫ (e).hom =
      (ProjectiveLineFieldExtension.pointIso K L).hom ≫
        extendedNode K L m hm (p) (q) (h) n f j k := by
  rw [standardNode, Category.assoc, Category.assoc, standardTranslation_comparison,
    PolygonStandardFieldExtension.node_iso_assoc]
  rfl

/-- Finite relabeling retains the original translated complete standard component. -/
theorem standardComponent_action (r : CyclicCharacteristicAtlas.RelabelGroup n) :
    standardComponent K L m hm n (f ≫ (action (G K m) n r).hom) j k =
      standardComponent K L m hm n f (r.2.2.symm j) k := by
  rw [standardComponent, standardTranslation_action, standardComponent]

/-- Finite relabeling retains the original translated standard node. -/
theorem standardNode_action (r : CyclicCharacteristicAtlas.RelabelGroup n) :
    standardNode K L m hm n (f ≫ (action (G K m) n r).hom) j k =
      standardNode K L m hm n f (r.2.2.symm j) k := by
  rw [standardNode, standardTranslation_action, standardNode]

end FLT.Mazur.PolygonCyclicBoundary

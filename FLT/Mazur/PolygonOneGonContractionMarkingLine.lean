/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOneGonContractionMarking
public import FLT.Mazur.PolygonSinglePointLineNormalization

/-!
# The actual retained Cartier line under polygon contraction

The full positive divisor line pulls back canonically along the non-flat
contraction. The comparison is the canonical dual ideal comparison and uses
the proved Cartier inverse image, without imposing a flatness hypothesis.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonOneGonContraction
open PolygonPinching PolygonMarkedSections PolygonSinglePointLineNormalization FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] contraction divisorLinePullbackIsoOfEq
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q) (i : Fin n)

/-- The original contraction has an invertible canonical comparison on the marking ideal. -/
theorem markingIdealComparison_isIso (a : Kˣ) :
    IsIso (idealModulePullbackHom
      (sectionMap K 1 (PolygonAtlas.normalization K 1) a 0).ker
      (contraction K n hn p q h i).left) := by
  apply idealModulePullbackHom_isIso_of_cartier _
    (section_cartier K 1 (PolygonAtlas.normalization K 1) (by decide)
      (PolygonAtlas.nodes K 1) (PolygonAtlas.isPushout K 1 (by decide)) a 0).1
  rw [section_contraction_ideal]
  exact (section_cartier K n p hn q h a i).1

/-- The actual positive marking line is the pullback of the actual one-gon marking line. -/
irreducible_def markingLineIso (a : Kˣ) :
    (Scheme.Modules.pullback (contraction K n hn p q h i).left).obj
      (pointLine K 1 (by decide) (PolygonAtlas.normalization K 1)
        (PolygonAtlas.nodes K 1) (PolygonAtlas.isPushout K 1 (by decide)) a 0) ≅
      pointLine K n hn p q h a i := by
  let _ := markingIdealComparison_isIso K n hn p q h i a
  exact divisorLinePullbackIsoOfEq _
    (section_cartier K 1 (PolygonAtlas.normalization K 1) (by decide)
      (PolygonAtlas.nodes K 1) (PolygonAtlas.isPushout K 1 (by decide)) a 0).1
    (section_cartier K n p hn q h a i).1 (section_contraction_ideal K n hn p q h i a)

end FLT.Mazur.PolygonOneGonContraction

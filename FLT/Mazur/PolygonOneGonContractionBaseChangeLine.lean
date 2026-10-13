/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonOneGonContractionCartierBaseChange
public import FLT.Mazur.PolygonOneGonContractionMarkingSection

/-!
# Cartier-line coherence for the descended base-changed contraction

The actual line on the original family pulls back along the descended
contraction. Its comparison preserves the canonical section and commutes with
the comparisons from the original split polygon and original target one-gon.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonOneGonContraction
open PolygonPinching PolygonMarkedSections FCurve
open PolygonMarkingBaseChange hiding markingLineIso markingLineIso_section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] contraction baseChangedContraction divisorLinePullbackIsoOfEq
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q) (i : Fin n)
  {T : Scheme} (g : T ⟶ Spec (.of K)) (a : Kˣ)

/-- Canonical positive marking-line comparison on the descended family contraction. -/
irreducible_def baseChangedMarkingLineIso :
    (Scheme.Modules.pullback (baseChangedContraction K n hn p q h i g).left).obj
      (markingLine K 1 (by decide) (PolygonAtlas.normalization K 1)
        (PolygonAtlas.nodes K 1) (PolygonAtlas.isPushout K 1 (by decide)) g a 0) ≅
      markingLine K n hn p q h g a i := by
  let _ := baseChangedContraction_markingIdeal_isIso K n hn p q h i g a
  exact divisorLinePullbackIsoOfEq _
    (markingIdeal_cartier K 1 (by decide) (PolygonAtlas.normalization K 1)
      (PolygonAtlas.nodes K 1) (PolygonAtlas.isPushout K 1 (by decide)) g a 0).1
    (markingIdeal_cartier K n hn p q h g a i).1
    (baseChangedContraction_ideal K n hn p q h i g a)

/-- The descended comparison preserves the original family marking section. -/
theorem baseChangedMarkingLineIso_section :
    DivisorLineSectionCompatible (baseChangedContraction K n hn p q h i g).left
      (markingIdeal_cartier K 1 (by decide) (PolygonAtlas.normalization K 1)
        (PolygonAtlas.nodes K 1) (PolygonAtlas.isPushout K 1 (by decide)) g a 0).1
      (markingIdeal_cartier K n hn p q h g a i).1
      (baseChangedMarkingLineIso K n hn p q h i g a) := by
  let _ := baseChangedContraction_markingIdeal_isIso K n hn p q h i g a
  rw [baseChangedMarkingLineIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

/-- The square of original and family line comparisons commutes on the actual sheaves. -/
theorem baseChangedMarkingLineIso_square :
    LinePullbackSquare (baseChangedContraction K n hn p q h i g).left
      (pullback.fst (PolygonAtlas.polygon K 1).hom g) (pullback.fst C.hom g)
      (contraction K n hn p q h i).left (baseChangedContraction_square K n hn p q h i g).w
      (PolygonMarkingBaseChange.markingLineIso K 1 (by decide)
        (PolygonAtlas.normalization K 1) (PolygonAtlas.nodes K 1)
        (PolygonAtlas.isPushout K 1 (by decide)) g a 0)
      (baseChangedMarkingLineIso K n hn p q h i g a) (markingLineIso K n hn p q h i a)
      (PolygonMarkingBaseChange.markingLineIso K n hn p q h g a i) :=
  divisorLineSectionCompatible_square _ _ _ _ _
    (PolygonMarkingBaseChange.markingLineIso_section K 1 (by decide)
      (PolygonAtlas.normalization K 1) (PolygonAtlas.nodes K 1)
      (PolygonAtlas.isPushout K 1 (by decide)) g a 0)
    (baseChangedMarkingLineIso_section K n hn p q h i g a)
    (markingLineIso_section K n hn p q h i a)
    (PolygonMarkingBaseChange.markingLineIso_section K n hn p q h g a i)

end FLT.Mazur.PolygonOneGonContraction

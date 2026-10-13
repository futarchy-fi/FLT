/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonMarkingBaseChange
public import FLT.Mazur.PolygonOneGonContractionBaseChange
public import FLT.Mazur.PolygonOneGonContractionMarking
public import FLT.Mazur.RelativeCartierMorphismBaseChange

/-!
# The original contraction marking under arbitrary base change

The contraction descended from the pulled-back pinching diagram preserves the
actual marked Cartier ideal over every parameter scheme. Both its source and
target are the original base-changed schemes.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonOneGonContraction
open PolygonPinching PolygonMarkedSections PolygonMarkingBaseChange FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] contraction baseChangedContraction
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q) (i : Fin n)
  {T : Scheme} (g : T ⟶ Spec (.of K))

/-- The descended map has the original Cartesian base-change square. -/
theorem baseChangedContraction_square :
    IsPullback (baseChangedContraction K n hn p q h i g).left
      (pullback.fst C.hom g) (pullback.fst (PolygonAtlas.polygon K 1).hom g)
      (contraction K n hn p q h i).left := by
  rw [baseChangedContraction_eq]
  exact OverPullbackLocalPushout.map_isPullback g _

/-- Pulling back the target family marking gives the original source family marking. -/
theorem baseChangedContraction_ideal (a : Kˣ) :
    (markingIdeal K 1 (PolygonAtlas.normalization K 1) g a 0).comap
        (baseChangedContraction K n hn p q h i g).left = markingIdeal K n p g a i := by
  rw [baseChangedContraction_eq]
  exact relativeCartierMorphismBaseChange_ideal _ g _ _
    (section_contraction_ideal K n hn p q h i a)

/-- The canonical marking-ideal comparison on the descended contraction is invertible. -/
theorem baseChangedContraction_markingIdeal_isIso (a : Kˣ) :
    IsIso (idealModulePullbackHom
      (markingIdeal K 1 (PolygonAtlas.normalization K 1) g a 0)
      (baseChangedContraction K n hn p q h i g).left) := by
  apply idealModulePullbackHom_isIso_of_cartier _
    (markingIdeal_cartier K 1 (by decide) (PolygonAtlas.normalization K 1)
      (PolygonAtlas.nodes K 1) (PolygonAtlas.isPushout K 1 (by decide)) g a 0).1
  rw [baseChangedContraction_ideal]
  exact (markingIdeal_cartier K n hn p q h g a i).1

end FLT.Mazur.PolygonOneGonContraction

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCyclicBoundaryDivisor
public import FLT.Mazur.PolygonOneGonContractionCartierBaseChange

/-!
# Actual contractions of the cyclically translated boundary polygons

Undo the specified translation and use the original descended contraction to
the one-gon. Pullback recovers the full translated marking ideal. The common
finite relabeling retains these actual maps and their Cartier-line comparisons.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonCyclicBoundary
open PolygonPinching PolygonUniversalAction PolygonParameterTranslation FCurve
open PolygonMarkingBaseChange PolygonOneGonContraction
open CyclicBoundaryParameter CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] translationIso markingIdeal movedMarkingIdeal
  baseChangedContraction contraction
variable (K : Type) [Field K] (m : ℕ) [NeZero m] (hm : 0 < m)
  {C : Over (Spec (.of K))} (p : components K m ⟶ C) (q : nodes K m ⟶ C)
  (h : IsPushout (toComponents K m hm) (toNodes K m) p q)
  (n : ℕ) [NeZero n] {T : Scheme} (g : T ⟶ Spec (.of K))
  (f : Over.mk g ⟶ parameter (G K m) n) (i : Fin m)
  (j : Multiplicative (ZMod n))
local notation "c" => markedSection (G K m) n g f (1, 1, j)

/-- The contraction of the original polygon translated by the actual cyclic parameter. -/
def labelContraction : (Over.pullback g).obj C ⟶
    (Over.pullback g).obj (PolygonAtlas.polygon K 1) :=
  (translationIso K m hm p q h g (c)).inv ≫ baseChangedContraction K m hm p q h i g

/-- Translating the original source recovers the original descended contraction exactly. -/
theorem translation_labelContraction :
    (translationIso K m hm p q h g (c)).hom ≫
      labelContraction K m hm p q h n g f i j =
        baseChangedContraction K m hm p q h i g := by
  rw [labelContraction, Iso.hom_inv_id_assoc]

/-- The actual contraction pulls the target marking back to the entire translated ideal. -/
theorem labelContraction_ideal (a : Kˣ) :
    (markingIdeal K 1 (PolygonAtlas.normalization K 1) g a 0).comap
      (labelContraction K m hm p q h n g f i j).left =
        labelIdeal K m hm p q h n g f a i j := by
  rw [labelContraction, Over.comp_left, Scheme.IdealSheafData.comap_comp,
    baseChangedContraction_ideal, labelIdeal, movedMarkingIdeal]

/-- Common relabeling retains the specified actual contraction for every cyclic label. -/
theorem labelContraction_action (e : RelabelGroup n) :
    labelContraction K m hm p q h n g (f ≫ (action (G K m) n e).hom) i j =
      labelContraction K m hm p q h n g f i (e.2.2.symm j) := by
  unfold labelContraction
  rw [section_action_cyclic]

/-- The canonical positive-line comparison along the actual translated contraction. -/
irreducible_def labelContractionLine (a : Kˣ) :
    (Scheme.Modules.pullback (labelContraction K m hm p q h n g f i j).left).obj
      (markingLine K 1 (by decide) (PolygonAtlas.normalization K 1)
        (PolygonAtlas.nodes K 1) (PolygonAtlas.isPushout K 1 (by decide)) g a 0) ≅
      divisorLineBundle (labelIdeal K m hm p q h n g f a i j)
        (labelIdeal_cartier K m hm p q h n g f a i j).1 := by
  let hs := (markingIdeal_cartier K 1 (by decide) (PolygonAtlas.normalization K 1)
    (PolygonAtlas.nodes K 1) (PolygonAtlas.isPushout K 1 (by decide)) g a 0).1
  let ht := (labelIdeal_cartier K m hm p q h n g f a i j).1
  let he := labelContraction_ideal K m hm p q h n g f i j a
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  exact divisorLinePullbackIsoOfEq _ hs ht he

/-- The contraction comparison preserves the canonical section on the full original schemes. -/
theorem labelContractionLine_section (a : Kˣ) :
    DivisorLineSectionCompatible (labelContraction K m hm p q h n g f i j).left
      (markingIdeal_cartier K 1 (by decide) (PolygonAtlas.normalization K 1)
        (PolygonAtlas.nodes K 1) (PolygonAtlas.isPushout K 1 (by decide)) g a 0).1
      (labelIdeal_cartier K m hm p q h n g f a i j).1
      (labelContractionLine K m hm p q h n g f i j a) := by
  let hs := (markingIdeal_cartier K 1 (by decide) (PolygonAtlas.normalization K 1)
    (PolygonAtlas.nodes K 1) (PolygonAtlas.isPushout K 1 (by decide)) g a 0).1
  let ht := (labelIdeal_cartier K m hm p q h n g f a i j).1
  let he := labelContraction_ideal K m hm p q h n g f i j a
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  rw [labelContractionLine_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

end FLT.Mazur.PolygonCyclicBoundary

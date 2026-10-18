/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCyclicBoundaryStandardTranslation
public import FLT.Mazur.PolygonContractionFieldExtension

/-!
# Actual cyclic boundary contraction on chosen standard field polygons

The independently chosen extension-field polygon contracts to the independently
chosen one-gon. Undoing its intrinsic translation commutes with both original
standard comparisons, so the entire original contraction is retained.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonCyclicBoundary
open PolygonPinching PolygonUniversalAction PolygonOneGonContraction
open CyclicBoundaryParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonParameterTranslation.translationIso
  contraction baseChangedContraction
variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (m : ℕ) [NeZero m] (hm : 0 < m) (n : ℕ) [NeZero n]
  (f : Over.mk (ProjectiveLineProductCharts.parameterToBase K L) ⟶
    CyclicBoundaryParameter.parameter (G K m) n)
  (i : Fin m) (j : Multiplicative (ZMod n))
local notation "p" => PolygonAtlas.normalization K m
local notation "q" => PolygonAtlas.nodes K m
local notation "h" => PolygonAtlas.isPushout K m hm
local notation "e" => PolygonStandardFieldExtension.iso K L m hm
local notation "e₁" => PolygonStandardFieldExtension.iso K L 1 (by decide)

/-- The actual translated standard polygon contracts to the chosen standard one-gon. -/
def standardContraction : PolygonAtlas.polygon L m ⟶ PolygonAtlas.polygon L 1 :=
  (standardTranslationIso K L m hm n f j).inv ≫
    contraction L m hm (PolygonAtlas.normalization L m) (PolygonAtlas.nodes L m)
      (PolygonAtlas.isPushout L m hm) i

/-- Undoing the specified translation recovers the original standard contraction. -/
@[reassoc] theorem standardTranslation_contraction :
    (standardTranslationIso K L m hm n f j).hom ≫
        standardContraction K L m hm n f i j =
      contraction L m hm (PolygonAtlas.normalization L m) (PolygonAtlas.nodes L m)
        (PolygonAtlas.isPushout L m hm) i := by
  rw [standardContraction, Iso.hom_inv_id_assoc]

/-- Both specified field comparisons retain the whole original translated contraction. -/
@[reassoc] theorem standardContraction_comparison :
    standardContraction K L m hm n f i j ≫ (e₁).hom =
      (e).hom ≫ extendedContraction K L m hm (p) (q) (h) n f i j := by
  rw [standardContraction, Category.assoc,
    PolygonContractionFieldExtension.baseChangedContraction_comparison]
  simp only [standardTranslationIso, Iso.trans_inv, Iso.symm_inv, Category.assoc,
    Iso.inv_hom_id_assoc]
  rfl

/-- The common finite relabeling preserves the chosen-standard contraction. -/
theorem standardContraction_action (r : CyclicCharacteristicAtlas.RelabelGroup n) :
    standardContraction K L m hm n (f ≫ (action (G K m) n r).hom) i j =
      standardContraction K L m hm n f i (r.2.2.symm j) := by
  rw [standardContraction, standardTranslation_action, standardContraction]

end FLT.Mazur.PolygonCyclicBoundary

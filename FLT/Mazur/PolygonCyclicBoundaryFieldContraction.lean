/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCyclicBoundaryFieldTranslation
public import FLT.Mazur.PolygonCyclicBoundaryContraction

/-!
# Contraction lines in intrinsic boundary field coordinates

The intrinsic field translation is an isomorphism. Its inverse gives the
original translated contraction, retaining the entire Cartier ideal and the
canonical line section, including when the original polygon is a one-gon.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonCyclicBoundary
open PolygonPinching PolygonUniversalAction PolygonParameterTranslation FCurve
open PolygonMarkingBaseChange PolygonOneGonContraction CyclicBoundaryParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] translationIso markingIdeal movedMarkingIdeal
variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (m : ℕ) [NeZero m] (hm : 0 < m)
  {C : Over (Spec (.of K))} (p : components K m ⟶ C) (q : nodes K m ⟶ C)
  (h : IsPushout (toComponents K m hm) (toNodes K m) p q)
  (n : ℕ) [NeZero n]
local notation "g" => ProjectiveLineProductCharts.parameterToBase K L
local notation "F" => Over.pullback (g)
variable (f : Over.mk (ProjectiveLineProductCharts.parameterToBase K L) ⟶
  CyclicBoundaryParameter.parameter (G K m) n)
  (a : Kˣ) (i : Fin m) (j : Multiplicative (ZMod n))
local notation "c" => markedSection (G K m) n (g) f (1, 1, j)

/-- The intrinsic translation with its original inverse on the entire pulled-back polygon. -/
def extendedTranslationIso : (F).obj C ≅ (F).obj C where
  hom := extendedTranslation K L m hm p q h n f j
  inv := (translationIso K m hm p q h (g) (c)).inv
  hom_inv_id := by rw [← extendedTranslation_iso_hom, Iso.hom_inv_id]
  inv_hom_id := by rw [← extendedTranslation_iso_hom, Iso.inv_hom_id]

/-- The intrinsic isomorphism is the original whole-polygon translation isomorphism. -/
theorem extendedTranslationIso_eq :
    extendedTranslationIso K L m hm p q h n f j =
      translationIso K m hm p q h (g) (c) := by
  apply Iso.ext
  exact (extendedTranslation_iso_hom K L m hm p q h n f j).symm

/-- Contract after undoing the intrinsic field-coordinate translation. -/
def extendedContraction : (F).obj C ⟶ (F).obj (PolygonAtlas.polygon K 1) :=
  (extendedTranslationIso K L m hm p q h n f j).inv ≫
    baseChangedContraction K m hm p q h i (g)

/-- The intrinsic contraction is precisely the original cyclic marking contraction. -/
theorem extendedContraction_eq :
    extendedContraction K L m hm p q h n f i j =
      labelContraction K m hm p q h n (g) f i j := rfl

/-- Translating before contraction recovers the entire original descended map. -/
@[reassoc] theorem extendedTranslation_contraction :
    extendedTranslation K L m hm p q h n f j ≫
        extendedContraction K L m hm p q h n f i j =
      baseChangedContraction K m hm p q h i (g) := by
  rw [← extendedTranslation_iso_hom, extendedContraction_eq, translation_labelContraction]

/-- The full original marked ideal survives the intrinsic translated contraction. -/
theorem extendedContraction_ideal :
    (markingIdeal K 1 (PolygonAtlas.normalization K 1) (g) a 0).comap
      (extendedContraction K L m hm p q h n f i j).left =
        labelIdeal K m hm p q h n (g) f a i j :=
  labelContraction_ideal K m hm p q h n (g) f i j a

/-- The original contraction line in the actual intrinsic field coordinates. -/
def extendedContractionLine :
    (Scheme.Modules.pullback (extendedContraction K L m hm p q h n f i j).left).obj
      (markingLine K 1 (by decide) (PolygonAtlas.normalization K 1)
        (PolygonAtlas.nodes K 1) (PolygonAtlas.isPushout K 1 (by decide)) (g) a 0) ≅
      divisorLineBundle (labelIdeal K m hm p q h n (g) f a i j)
        (labelIdeal_cartier K m hm p q h n (g) f a i j).1 :=
  labelContractionLine K m hm p q h n (g) f i j a

/-- Intrinsic field-coordinate contraction preserves the exact canonical line section. -/
theorem extendedContractionLine_section :
    DivisorLineSectionCompatible (extendedContraction K L m hm p q h n f i j).left
      (markingIdeal_cartier K 1 (by decide) (PolygonAtlas.normalization K 1)
        (PolygonAtlas.nodes K 1) (PolygonAtlas.isPushout K 1 (by decide)) (g) a 0).1
      (labelIdeal_cartier K m hm p q h n (g) f a i j).1
      (extendedContractionLine K L m hm p q h n f a i j) :=
  labelContractionLine_section K m hm p q h n (g) f i j a

/-- The common finite relabeling retains the whole intrinsic contraction. -/
theorem extendedContraction_action (r : CyclicCharacteristicAtlas.RelabelGroup n) :
    extendedContraction K L m hm p q h n (f ≫ (action (G K m) n r).hom) i j =
      extendedContraction K L m hm p q h n f i (r.2.2.symm j) :=
  labelContraction_action K m hm p q h n (g) f i j r

end FLT.Mazur.PolygonCyclicBoundary

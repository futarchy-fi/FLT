/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCyclicBoundaryFieldTranslation
public import FLT.Mazur.PolygonCyclicBoundaryDivisor
public import FLT.Mazur.PolygonParameterNormalizationLine

/-!
# Normalization lines in the actual boundary field coordinates

The intrinsic field action retains the original normalization component maps
and their section-preserving marking lines. The specified projective-line
coefficient comparison identifies these maps with the extension-field cocone.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonCyclicBoundary
open PolygonPinching PolygonUniversalAction PolygonParameterTranslation FCurve
open PolygonMarkingBaseChange CyclicBoundaryParameter
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
  (a : Kˣ) (i : Fin m) (j : Multiplicative (ZMod n)) (k : Fin m)
local notation "c" => markedSection (G K m) n (g) f (1, 1, j)

/-- The original component followed by the intrinsic extension-field translation. -/
def extendedComponent : (F).obj (component K) ⟶ (F).obj C :=
  (F).map (componentι K m k ≫ p) ≫ extendedTranslation K L m hm p q h n f j

/-- The normalization map in the original translation coordinates is unchanged. -/
theorem extendedComponent_eq :
    extendedComponent K L m hm p q h n f j k =
      (F).map (componentι K m k ≫ p) ≫ (translationIso K m hm p q h (g) (c)).hom := by
  rw [extendedComponent, extendedTranslation_iso_hom]

/-- The specified coefficient change intertwines the intrinsic component maps. -/
@[reassoc] theorem extendedComponent_coordinates :
    (ProjectiveLineFieldExtension.componentIso K L).hom ≫
        extendedComponent K L m hm p q h n f j k =
      componentι L m k ≫ PolygonActionFieldExtension.normalization K L m p ≫
        extendedTranslation K L m hm p q h n f j := by
  rw [extendedComponent, ← Category.assoc,
    ← PolygonActionFieldExtension.component_normalization, Category.assoc]

/-- The original component marking line in intrinsic extension-field action coordinates. -/
def extendedNormalizationLine :
    (Scheme.Modules.pullback (extendedComponent K L m hm p q h n f j k).left).obj
      (divisorLineBundle (labelIdeal K m hm p q h n (g) f a i j)
        (labelIdeal_cartier K m hm p q h n (g) f a i j).1) ≅
      normalizationMarkingLine K m hm p q h a i k (g) :=
  (Scheme.Modules.pullbackCongr (by rw [extendedComponent_eq, Over.comp_left])).app _ ≪≫
    movedNormalizationLineIso K m hm p q h (g) (c) a i k

/-- Intrinsic field coordinates preserve the complete canonical component section. -/
theorem extendedNormalizationLine_section :
    DivisorLineSectionCompatible (extendedComponent K L m hm p q h n f j k).left
      (labelIdeal_cartier K m hm p q h n (g) f a i j).1
      (relativeCartierBaseChange (component K).hom (g) _
        (normalizationIdeal_relativeCartier K m hm p q h a i k)).1
      (extendedNormalizationLine K L m hm p q h n f a i j k) := by
  exact (movedNormalizationLineIso_section K m hm p q h (g) (c) a i k).congr _

end FLT.Mazur.PolygonCyclicBoundary

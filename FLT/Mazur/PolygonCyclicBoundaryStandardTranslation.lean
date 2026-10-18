/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCyclicBoundaryFieldContraction
public import FLT.Mazur.PolygonActionCoconeNaturality
public import FLT.Mazur.PolygonStandardFieldExtension

/-!
# Actual boundary translations on the chosen standard extension-field polygon

The standard-polygon comparison conjugates the original translation. Its hom
is exactly the intrinsic action on the independently chosen standard polygon,
with the actual cyclic parameter section in the extension-field split group.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonCyclicBoundary
open PolygonPinching PolygonUniversalAction CyclicBoundaryParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonParameterTranslation.translationIso
variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (m : ℕ) [NeZero m] (hm : 0 < m) (n : ℕ) [NeZero n]
  (f : Over.mk (ProjectiveLineProductCharts.parameterToBase K L) ⟶
    CyclicBoundaryParameter.parameter (G K m) n) (j : Multiplicative (ZMod n))
local notation "p" => PolygonAtlas.normalization K m
local notation "q" => PolygonAtlas.nodes K m
local notation "h" => PolygonAtlas.isPushout K m hm
local notation "e" => PolygonStandardFieldExtension.iso K L m hm

/-- The actual translation on the independently chosen extension-field polygon. -/
def standardTranslationIso : PolygonAtlas.polygon L m ≅ PolygonAtlas.polygon L m :=
  (e) ≪≫ extendedTranslationIso K L m hm (p) (q) (h) n f j ≪≫ (e).symm

/-- The specified standard comparison intertwines the entire original intrinsic translation. -/
@[reassoc] theorem standardTranslation_comparison :
    (standardTranslationIso K L m hm n f j).hom ≫ (e).hom =
      (e).hom ≫ extendedTranslation K L m hm (p) (q) (h) n f j := by
  simp only [standardTranslationIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- Conjugation agrees with the actual descended action on the chosen standard polygon. -/
theorem standardTranslation_hom :
    (standardTranslationIso K L m hm n f j).hom =
      (λ_ (PolygonAtlas.polygon L m)).inv ≫
        extendedParameter K L m n f j ▷ PolygonAtlas.polygon L m ≫
          act L m hm (PolygonAtlas.normalization L m) (PolygonAtlas.nodes L m)
            (PolygonAtlas.isPushout L m hm) := by
  apply (cancel_mono (e).hom).mp
  rw [standardTranslation_comparison]
  exact (PolygonActionCoconeNaturality.translation_natural L m hm
    (PolygonAtlas.normalization L m) (PolygonAtlas.nodes L m)
    (PolygonAtlas.isPushout L m hm)
    (PolygonActionFieldExtension.normalization K L m (p))
    (PolygonActionFieldExtension.nodeMap K L m (q))
    (PolygonActionFieldExtension.cocone K L m hm (p) (q) (h)) (e).hom
    (PolygonStandardFieldExtension.normalization_iso K L m hm)
    (extendedParameter K L m n f j)).symm

/-- Common finite relabeling retains the entire chosen-standard translation isomorphism. -/
theorem standardTranslation_action (r : CyclicCharacteristicAtlas.RelabelGroup n) :
    standardTranslationIso K L m hm n (f ≫ (action (G K m) n r).hom) j =
      standardTranslationIso K L m hm n f (r.2.2.symm j) := by
  apply Iso.ext
  rw [standardTranslation_hom, standardTranslation_hom, extendedParameter_action]

end FLT.Mazur.PolygonCyclicBoundary

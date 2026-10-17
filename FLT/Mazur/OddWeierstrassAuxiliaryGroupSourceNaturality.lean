/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassAuxiliaryNormalizationCubic
public import FLT.Mazur.OddWeierstrassAuxiliaryCubicNaturality

/-!
# Full normalization commutes with every source morphism

The actual proper coefficient square descends through the original coefficient
comparisons and the canonical global-sections maps. Both directions of the full
normalization group comparison commute with arbitrary changes of source scheme.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {T U : Scheme} (f : T ⟶ levelThree.left) (k : U ⟶ T)

/-- The inverse of actual full normalization commutes with every original source map. -/
@[reassoc] theorem auxiliarySchemeNormalizationGroupIso_inv_natural :
    auxiliarySchemeOriginalSourceMap f k ≫
        (auxiliarySchemeNormalizationGroupIso f).inv.hom.hom.hom.left =
      (auxiliarySchemeNormalizationGroupIso (k ≫ f)).inv.hom.hom.hom.left ≫
        auxiliarySchemeNormalizedSourceMap f k := by
  apply auxiliarySchemeNormalizedCubicProjection_hom_ext f
  · have hp : auxiliaryOriginalCoefficientTransition f.appTop.hom k.appTop.hom ≫
        (auxiliaryProperNormalization f.appTop.hom).inv =
      (auxiliaryProperNormalization (k ≫ f).appTop.hom).inv ≫
        auxiliaryNormalizedCoefficientTransition f.appTop.hom k.appTop.hom :=
      (auxiliaryProperNormalization_inv_natural f.appTop.hom k.appTop.hom).symm
    rw [Category.assoc, auxiliarySchemeNormalizationGroupIso_inv_cubic,
      ← auxiliarySchemeOriginalCubicProjection_natural_assoc, Category.assoc, hp,
      ← auxiliarySchemeNormalizedCubicProjection_natural,
      auxiliarySchemeNormalizationGroupIso_inv_cubic_assoc]
  · rw [Category.assoc, (auxiliarySchemeNormalizationGroupIso f).inv.hom.hom.hom.w,
      auxiliarySchemeOriginalSourceMap_snd, Category.assoc,
      auxiliarySchemeNormalizedSourceMap_snd,
      ← Category.assoc, (auxiliarySchemeNormalizationGroupIso (k ≫ f)).inv.hom.hom.hom.w]

/-- The forward actual full normalization commutes with every original source map. -/
@[reassoc] theorem auxiliarySchemeNormalizationGroupIso_hom_natural :
    auxiliarySchemeNormalizedSourceMap f k ≫
        (auxiliarySchemeNormalizationGroupIso f).hom.hom.hom.hom.left =
      (auxiliarySchemeNormalizationGroupIso (k ≫ f)).hom.hom.hom.hom.left ≫
        auxiliarySchemeOriginalSourceMap f k := by
  apply auxiliarySchemeOriginalCubicProjection_hom_ext f
  · have hp : auxiliaryNormalizedCoefficientTransition f.appTop.hom k.appTop.hom ≫
        (auxiliaryProperNormalization f.appTop.hom).hom =
      (auxiliaryProperNormalization (k ≫ f).appTop.hom).hom ≫
        auxiliaryOriginalCoefficientTransition f.appTop.hom k.appTop.hom :=
      auxiliaryProperNormalization_natural f.appTop.hom k.appTop.hom
    rw [Category.assoc, auxiliarySchemeNormalizationGroupIso_hom_cubic,
      ← auxiliarySchemeNormalizedCubicProjection_natural_assoc, Category.assoc, hp,
      ← auxiliarySchemeOriginalCubicProjection_natural,
      auxiliarySchemeNormalizationGroupIso_hom_cubic_assoc]
  · rw [Category.assoc, (auxiliarySchemeNormalizationGroupIso f).hom.hom.hom.hom.w,
      auxiliarySchemeNormalizedSourceMap_snd, Category.assoc,
      auxiliarySchemeOriginalSourceMap_snd,
      ← Category.assoc, (auxiliarySchemeNormalizationGroupIso (k ≫ f)).hom.hom.hom.hom.w]

end FLT.Mazur.OddWeierstrassParameter

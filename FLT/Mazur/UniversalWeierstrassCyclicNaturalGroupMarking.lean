/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassCyclicNaturalGroup

/-!
# Full marking compatibility on the actual natural group families

On every arbitrary source scheme, the actual normalization group isomorphism
carries each actual normalized full marking to the original marking. This
compares sections of the actual source families, including every cyclic label.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.UniversalWeierstrass
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n] {T : Scheme} (f : T ⟶ (cyclicAuxiliaryScheme n).left)
local notation "aO" => cyclicSchemeAuxiliaryPoint n (𝟙 _)
local notation "aN" => auxiliarySchemeNormalizedPoint aO

/-- The original arbitrary source viewed over the universal full parameter scheme. -/
def cyclicNaturalSourcePoint : Over.mk f ⟶ 𝟙_ (Over (cyclicAuxiliaryScheme n).left) :=
  Over.homMk f (Category.comp_id _)

/-- The original global full section pulled back to the actual source scheme. -/
def cyclicNaturalOriginalSection (c : CyclicLabels n) :
    𝟙_ (Over T) ⟶ ((Over.pullback f).mapCommGrp.obj (auxiliarySchemeGroup aO)).X :=
  OverPullbackSection.lift f (auxiliarySchemeGroup aO).X
    (cyclicNaturalSourcePoint n f ≫ cyclicSchemeOriginalMarking n (𝟙 _) c)

/-- The normalized global full section pulled back to the actual source scheme. -/
def cyclicNaturalNormalizedSection (c : CyclicLabels n) :
    𝟙_ (Over T) ⟶ ((Over.pullback f).mapCommGrp.obj (auxiliarySchemeGroup aN)).X :=
  OverPullbackSection.lift f (auxiliarySchemeGroup aN).X
    (cyclicNaturalSourcePoint n f ≫ cyclicSchemeNormalizedMarking n (𝟙 _) c)

/-- The original coefficient comparison identifies the actual source full marking. -/
theorem cyclicNaturalOriginalGroupIso_marking (c : CyclicLabels n) :
    cyclicNaturalOriginalSection n f c ≫
      (cyclicNaturalOriginalGroupIso n f).hom.hom.hom.hom =
        cyclicSchemeOriginalMarking n f c := by
  apply OverPullbackSection.hom_ext
    (cyclicSchemeAuxiliaryPoint n f ≫ levelFour.hom) universalGroup
  rw [Over.comp_left, Category.assoc, cyclicNaturalOriginalGroupIso_fst,
    ← Category.assoc]
  rw [cyclicNaturalOriginalSection, OverPullbackSection.lift_fst,
    Over.comp_left, Category.assoc, cyclicSchemeOriginalMarking_fst,
    cyclicSchemeOriginalMarking_fst, Category.id_comp]
  rfl

/-- The normalized coefficient comparison identifies every actual normalized source label. -/
theorem cyclicNaturalNormalizedGroupIso_marking (c : CyclicLabels n) :
    cyclicNaturalNormalizedSection n f c ≫
      (cyclicNaturalNormalizedGroupIso n f).hom.hom.hom.hom =
        cyclicSchemeOriginalMarking n (f ≫ cyclicNormalizationMap n) c := by
  apply OverPullbackSection.hom_ext
    (cyclicSchemeAuxiliaryPoint n (f ≫ cyclicNormalizationMap n) ≫ levelFour.hom) universalGroup
  rw [Over.comp_left, Category.assoc, cyclicNaturalNormalizedGroupIso_fst,
    ← Category.assoc]
  rw [cyclicNaturalNormalizedSection, OverPullbackSection.lift_fst,
    Over.comp_left, Category.assoc, cyclicSchemeNormalizedMarking_fst,
    cyclicSchemeOriginalMarking_fst, Category.assoc]
  rfl

/-- Pulling back the actual global comparison retains each complete marking equation. -/
theorem cyclicNaturalNormalization_lift_marking (c : CyclicLabels n) :
    cyclicNaturalNormalizedSection n f c ≫
      ((Over.pullback f).mapCommGrp.map
        (auxiliarySchemeNormalizationGroupIso aO).hom).hom.hom.hom =
          cyclicNaturalOriginalSection n f c := by
  unfold cyclicNaturalNormalizedSection cyclicNaturalOriginalSection
  apply GroupSchemeBaseChange.lift_map_eq f (auxiliarySchemeNormalizationGroupIso aO).hom
  rw [Category.assoc, cyclicSchemeNormalizedMarking_compare]

/-- The actual natural normalization group isomorphism preserves all source-family labels. -/
theorem cyclicNaturalNormalizationGroupIso_marking (c : CyclicLabels n) :
    cyclicSchemeOriginalMarking n (f ≫ cyclicNormalizationMap n) c ≫
      (cyclicNaturalNormalizationGroupIso n f).hom.hom.hom.hom =
        cyclicSchemeOriginalMarking n f c := by
  let eN := (CommGrp.forget (Over T)).mapIso (cyclicNaturalNormalizedGroupIso n f)
  let eO := (CommGrp.forget (Over T)).mapIso (cyclicNaturalOriginalGroupIso n f)
  let m := ((Over.pullback f).mapCommGrp.map
    (auxiliarySchemeNormalizationGroupIso aO).hom).hom.hom.hom
  have hN : cyclicNaturalNormalizedSection n f c ≫ eN.hom =
      cyclicSchemeOriginalMarking n (f ≫ cyclicNormalizationMap n) c :=
    cyclicNaturalNormalizedGroupIso_marking n f c
  have hO : cyclicNaturalOriginalSection n f c ≫ eO.hom =
      cyclicSchemeOriginalMarking n f c := cyclicNaturalOriginalGroupIso_marking n f c
  have hM : cyclicNaturalNormalizedSection n f c ≫ m = cyclicNaturalOriginalSection n f c :=
    cyclicNaturalNormalization_lift_marking n f c
  rw [cyclicNaturalNormalizationGroupIso_def]
  change _ ≫ (eN.inv ≫ m ≫ eO.hom) = _
  rw [← hN, Category.assoc, eN.hom_inv_id_assoc, ← Category.assoc, hM, hO]

end FLT.Mazur.UniversalWeierstrass

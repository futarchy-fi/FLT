/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassCyclicNormalizationMapLabels

/-!
# Actual group families for natural full normalization

Pulling back the global normalization group isomorphism compares the actual
original and normalized full families over every scheme. The comparison uses
the original coefficient maps and the canonical composition of pullbacks.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n] {T : Scheme} (f : T ⟶ (cyclicAuxiliaryScheme n).left)
local notation "aO" => cyclicSchemeAuxiliaryPoint n (𝟙 _)
local notation "aN" => auxiliarySchemeNormalizedPoint aO
local notation "G" => integralCurveGroup smoothEquation smoothEquation_discriminant

/-- The original coefficient maps agree on the actual arbitrary source family. -/
theorem cyclicNaturalOriginalGroup_base :
    f ≫ (aO ≫ levelFour.hom) = cyclicSchemeAuxiliaryPoint n f ≫ levelFour.hom := by
  simp only [cyclicSchemeAuxiliaryPoint, Category.id_comp, Category.assoc]

/-- The normalized coefficient maps agree on the actual arbitrary source family. -/
theorem cyclicNaturalNormalizedGroup_base :
    f ≫ (aN ≫ levelFour.hom) =
      cyclicSchemeAuxiliaryPoint n (f ≫ cyclicNormalizationMap n) ≫ levelFour.hom := by
  change _ = ((f ≫ cyclicNormalizationMap n) ≫ (forgetCyclic n).left) ≫ levelFour.hom
  rw [Category.assoc f, cyclicNormalizationMap_forget]
  simp only [cyclicSchemeAuxiliaryPoint, Category.id_comp, Category.assoc]

/-- The actual original source family is the pullback of the original universal source group. -/
irreducible_def cyclicNaturalOriginalGroupIso :
    (Over.pullback f).mapCommGrp.obj (auxiliarySchemeGroup aO) ≅
      auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n f) :=
  (GroupSchemeBaseChange.compIso f (aO ≫ levelFour.hom) G).symm ≪≫
    GroupSchemeBaseChange.congrIso (cyclicNaturalOriginalGroup_base n f) G

/-- The actual normalized source family is the pullback of the normalized universal group. -/
irreducible_def cyclicNaturalNormalizedGroupIso :
    (Over.pullback f).mapCommGrp.obj (auxiliarySchemeGroup aN) ≅
      auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n (f ≫ cyclicNormalizationMap n)) :=
  (GroupSchemeBaseChange.compIso f (aN ≫ levelFour.hom) G).symm ≪≫
    GroupSchemeBaseChange.congrIso (cyclicNaturalNormalizedGroup_base n f) G

/-- Natural full normalization compares the actual group families on every source scheme. -/
irreducible_def cyclicNaturalNormalizationGroupIso :
    auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n (f ≫ cyclicNormalizationMap n)) ≅
      auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n f) :=
  (cyclicNaturalNormalizedGroupIso n f).symm ≪≫
    (Over.pullback f).mapCommGrp.mapIso (auxiliarySchemeNormalizationGroupIso aO) ≪≫
    cyclicNaturalOriginalGroupIso n f

/-- The original coefficient comparison retains the actual universal projection. -/
@[reassoc] theorem cyclicNaturalOriginalGroupIso_fst :
    (cyclicNaturalOriginalGroupIso n f).hom.hom.hom.hom.left ≫
      pullback.fst universalGroup.hom (cyclicSchemeAuxiliaryPoint n f ≫ levelFour.hom) =
        pullback.fst (auxiliarySchemeGroup aO).X.hom f ≫
          pullback.fst universalGroup.hom (aO ≫ levelFour.hom) := by
  rw [cyclicNaturalOriginalGroupIso_def]
  change (_ ≫ _) ≫ _ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z ↦
      (GroupSchemeBaseChange.compIso f (aO ≫ levelFour.hom) G).inv.hom.hom.hom.left ≫ z)
        (GroupSchemeBaseChange.congrIso_hom_fst (cyclicNaturalOriginalGroup_base n f) G)).trans
          (GroupSchemeBaseChange.compIso_inv_fst f (aO ≫ levelFour.hom) G))

/-- The normalized coefficient comparison retains the actual normalized projection. -/
@[reassoc] theorem cyclicNaturalNormalizedGroupIso_fst :
    (cyclicNaturalNormalizedGroupIso n f).hom.hom.hom.hom.left ≫
      pullback.fst universalGroup.hom
        (cyclicSchemeAuxiliaryPoint n (f ≫ cyclicNormalizationMap n) ≫ levelFour.hom) =
          pullback.fst (auxiliarySchemeGroup aN).X.hom f ≫
            pullback.fst universalGroup.hom (aN ≫ levelFour.hom) := by
  rw [cyclicNaturalNormalizedGroupIso_def]
  change (_ ≫ _) ≫ _ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z ↦
      (GroupSchemeBaseChange.compIso f (aN ≫ levelFour.hom) G).inv.hom.hom.hom.left ≫ z)
        (GroupSchemeBaseChange.congrIso_hom_fst (cyclicNaturalNormalizedGroup_base n f) G)).trans
          (GroupSchemeBaseChange.compIso_inv_fst f (aN ≫ levelFour.hom) G))

end FLT.Mazur.UniversalWeierstrass

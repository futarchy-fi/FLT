/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassFullNormalizationParameter

/-!
# Actual normalized points with the entire cyclic auxiliary marking

Every original full point on every source scheme determines a normalized full
point. The construction retains the auxiliary point used for normalization,
the actual coefficient map, and each label of the original product group.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.UniversalWeierstrass
open AuxiliaryLevel WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n] {T : Scheme} (f : T ⟶ (cyclicAuxiliaryScheme n).left)

/-- The actual auxiliary point underlying the original complete cyclic point. -/
def cyclicSchemeAuxiliaryPoint : T ⟶ levelFour.left := f ≫ (forgetCyclic n).left

/-- The full original point over the coefficient map of its auxiliary point. -/
def cyclicSchemeGroupPoint :
    (Over.map (cyclicSchemeAuxiliaryPoint n f ≫ levelFour.hom)).obj
      (𝟙_ (Over T)) ⟶ cyclicAuxiliaryScheme n :=
  Over.homMk f (by
    dsimp [cyclicSchemeAuxiliaryPoint]
    rw [Category.id_comp, Category.assoc, (forgetCyclic n).w])

/-- The complete faithful marking on the actual original source family. -/
def cyclicSchemeOriginalParameter :
    𝟙_ (Over T) ⟶ faithfulScheme (auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n f)).X
      (CyclicLabels n) :=
  auxiliarySchemeFullOriginalParameter (cyclicSchemeAuxiliaryPoint n f) (CyclicLabels n)
    (cyclicSchemeGroupPoint n f)

/-- The complete normalized parameter, retaining its actual normalized coefficient map. -/
def cyclicSchemeNormalizedParameter :
    (Over.map (auxiliarySchemeNormalizedPoint (cyclicSchemeAuxiliaryPoint n f) ≫
      levelFour.hom)).obj (𝟙_ (Over T)) ⟶ cyclicAuxiliaryScheme n :=
  auxiliarySchemeFullNormalizedParameter (cyclicSchemeAuxiliaryPoint n f) (CyclicLabels n)
    (cyclicSchemeGroupPoint n f)

/-- Normalization of an actual full cyclic point on any scheme. -/
def cyclicSchemeNormalizedPoint : T ⟶ (cyclicAuxiliaryScheme n).left :=
  (cyclicSchemeNormalizedParameter n f).left

/-- The original full point is normalized over exactly the auxiliary normalization base. -/
@[reassoc] theorem cyclicSchemeNormalizedPoint_base :
    cyclicSchemeNormalizedPoint n f ≫ (cyclicAuxiliaryScheme n).hom =
      auxiliarySchemeNormalizedPoint (cyclicSchemeAuxiliaryPoint n f) ≫ levelFour.hom := by
  exact (cyclicSchemeNormalizedParameter n f).w.trans (Category.id_comp _)

/-- Every full label retains the actual normalization comparison and original parameter. -/
theorem cyclicSchemeNormalizedPoint_value (c : CyclicLabels n) :
    cyclicSchemeNormalizedPoint n f ≫
      (cyclicAuxiliaryInclusion n ≫ value universalGroup (CyclicLabels n) c).left =
        (cyclicSchemeOriginalParameter n f ≫ faithfulInclusion
          (auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n f)).X (CyclicLabels n) ≫
            value (auxiliarySchemeGroup (cyclicSchemeAuxiliaryPoint n f)).X
              (CyclicLabels n) c).left ≫
                (auxiliarySchemeNormalizationGroupIso
                  (cyclicSchemeAuxiliaryPoint n f)).inv.hom.hom.hom.left ≫
                    pullback.fst universalGroup.hom
                      (auxiliarySchemeNormalizedPoint (cyclicSchemeAuxiliaryPoint n f) ≫
                        levelFour.hom) :=
  auxiliarySchemeFullNormalizedParameter_value (cyclicSchemeAuxiliaryPoint n f)
    (CyclicLabels n) (cyclicSchemeGroupPoint n f) c

end FLT.Mazur.UniversalWeierstrass

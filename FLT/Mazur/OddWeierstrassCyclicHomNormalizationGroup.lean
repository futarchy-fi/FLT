/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomNormalizationParameter
public import FLT.Mazur.OddWeierstrassCyclicHomSourceModuli
public import FLT.Mazur.GroupSchemeBaseChangeComposition

/-!
# Independent normalization preserves the actual source cyclic sections

Compare the reconstructed normalized source first with the auxiliary normalized
group, then with the original group. Projection identifies every cyclic section.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
open IntegralWeierstrassParameter (oddChartEquation oddChart_discriminant)
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme}
  (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)
local notation "a" => cyclicHomAuxiliaryPoint n f
local notation "fN" => cyclicHomNormalizedPoint n f
local notation "aN" => auxiliarySchemeNormalizedPoint a
local notation "G" => integralCurveGroup oddChartEquation oddChart_discriminant

/-- Reconstructing the normalized source retains the exact normalized auxiliary base. -/
theorem cyclicHomNormalization_base :
    cyclicHomAuxiliaryPoint n fN ≫ levelThree.hom = aN ≫ levelThree.hom :=
  congrArg (fun g ↦ g ≫ levelThree.hom) (cyclicHomNormalizedPoint_auxiliary n f)

/-- Compare the reconstructed source group with the established auxiliary normalized group. -/
def cyclicHomNormalizationBaseIso :
    auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n fN) ≅ auxiliarySchemeGroup aN :=
  GroupSchemeBaseChange.congrIso (cyclicHomNormalization_base n f) G

/-- The source comparison retains the actual projection to the universal group. -/
@[reassoc] theorem cyclicHomNormalizationBaseIso_fst :
    (cyclicHomNormalizationBaseIso n f).hom.hom.hom.hom.left ≫
      pullback.fst universalGroup.hom (aN ≫ levelThree.hom) =
        pullback.fst universalGroup.hom
          (cyclicHomAuxiliaryPoint n fN ≫ levelThree.hom) :=
  GroupSchemeBaseChange.congrIso_hom_fst (cyclicHomNormalization_base n f) G

/-- The full normalized source group is isomorphic to the original source group. -/
irreducible_def cyclicHomNormalizationGroupIso :
    auxiliarySchemeGroup (cyclicHomAuxiliaryPoint n fN) ≅ auxiliarySchemeGroup a :=
  cyclicHomNormalizationBaseIso n f ≪≫ auxiliarySchemeNormalizationGroupIso a

/-- The intermediate comparison retains the transported original cyclic section. -/
theorem cyclicHomNormalizationBaseIso_marking (b : Multiplicative (ZMod n)) :
    cyclicHomSourceMarking n fN b ≫
      (cyclicHomNormalizationBaseIso n f).hom.hom.hom.hom =
        cyclicHomSourceMarking n f b ≫
          (auxiliarySchemeNormalizationGroupIso a).inv.hom.hom.hom := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (cyclicHomSourceMarking n fN b ≫
      (cyclicHomNormalizationBaseIso n f).hom.hom.hom.hom).left ≫
        pullback.fst universalGroup.hom (aN ≫ levelThree.hom) =
      (cyclicHomSourceMarking n f b ≫
        (auxiliarySchemeNormalizationGroupIso a).inv.hom.hom.hom).left ≫
          pullback.fst universalGroup.hom (aN ≫ levelThree.hom)
    rw [Over.comp_left, Over.comp_left, Category.assoc,
      cyclicHomNormalizationBaseIso_fst, cyclicHomSourceMarking_fst,
      cyclicHomNormalizedPoint_value, Category.assoc]
  · exact (cyclicHomSourceMarking n fN b ≫
      (cyclicHomNormalizationBaseIso n f).hom.hom.hom.hom).w.trans
        (cyclicHomSourceMarking n f b ≫
          (auxiliarySchemeNormalizationGroupIso a).inv.hom.hom.hom).w.symm

/-- The normalization isomorphism identifies every normalized cyclic section with its original. -/
theorem cyclicHomNormalizationGroupIso_marking (b : Multiplicative (ZMod n)) :
    cyclicHomSourceMarking n fN b ≫
      (cyclicHomNormalizationGroupIso n f).hom.hom.hom.hom =
        cyclicHomSourceMarking n f b := by
  rw [cyclicHomNormalizationGroupIso_def]
  change cyclicHomSourceMarking n fN b ≫
    (cyclicHomNormalizationBaseIso n f).hom.hom.hom.hom ≫
      (auxiliarySchemeNormalizationGroupIso a).hom.hom.hom.hom = _
  rw [← Category.assoc, cyclicHomNormalizationBaseIso_marking, Category.assoc]
  let e := (CommGrp.forget _).mapIso (auxiliarySchemeNormalizationGroupIso a)
  change cyclicHomSourceMarking n f b ≫ e.inv ≫ e.hom = _
  rw [e.inv_hom_id]
  exact Category.comp_id _

end FLT.Mazur.OddWeierstrassParameter

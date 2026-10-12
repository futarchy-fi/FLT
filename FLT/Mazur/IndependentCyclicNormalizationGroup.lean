/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IndependentCyclicNormalizationParameter
public import FLT.Mazur.IndependentCyclicSourceModuli
public import FLT.Mazur.GroupSchemeBaseChangeComposition

/-!
# Independent normalization preserves the actual source cyclic sections

Compare the reconstructed normalized source first with the auxiliary normalized
group, then with the original group. Projection identifies every cyclic section.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.UniversalWeierstrass
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme}
  (f : T ⟶ (independentCyclicAuxiliaryScheme n).left)
local notation "a" => independentCyclicAuxiliaryPoint n f
local notation "fN" => independentCyclicNormalizedPoint n f
local notation "aN" => auxiliarySchemeNormalizedPoint a
local notation "G" => integralCurveGroup smoothEquation smoothEquation_discriminant

/-- Reconstructing the normalized source retains the exact normalized auxiliary base. -/
theorem independentCyclicNormalization_base :
    independentCyclicAuxiliaryPoint n fN ≫ levelFour.hom = aN ≫ levelFour.hom :=
  congrArg (fun g ↦ g ≫ levelFour.hom) (independentCyclicNormalizedPoint_auxiliary n f)

/-- Compare the reconstructed source group with the established auxiliary normalized group. -/
def independentCyclicNormalizationBaseIso :
    auxiliarySchemeGroup (independentCyclicAuxiliaryPoint n fN) ≅ auxiliarySchemeGroup aN :=
  GroupSchemeBaseChange.congrIso (independentCyclicNormalization_base n f) G

/-- The source comparison retains the actual projection to the universal group. -/
@[reassoc] theorem independentCyclicNormalizationBaseIso_fst :
    (independentCyclicNormalizationBaseIso n f).hom.hom.hom.hom.left ≫
      pullback.fst universalGroup.hom (aN ≫ levelFour.hom) =
        pullback.fst universalGroup.hom
          (independentCyclicAuxiliaryPoint n fN ≫ levelFour.hom) :=
  GroupSchemeBaseChange.congrIso_hom_fst (independentCyclicNormalization_base n f) G

/-- The full normalized source group is isomorphic to the original source group. -/
irreducible_def independentCyclicNormalizationGroupIso :
    auxiliarySchemeGroup (independentCyclicAuxiliaryPoint n fN) ≅ auxiliarySchemeGroup a :=
  independentCyclicNormalizationBaseIso n f ≪≫ auxiliarySchemeNormalizationGroupIso a

/-- The intermediate comparison retains the transported original cyclic section. -/
theorem independentCyclicNormalizationBaseIso_marking (b : Multiplicative (ZMod n)) :
    independentCyclicSourceMarking n fN b ≫
      (independentCyclicNormalizationBaseIso n f).hom.hom.hom.hom =
        independentCyclicSourceMarking n f b ≫
          (auxiliarySchemeNormalizationGroupIso a).inv.hom.hom.hom := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (independentCyclicSourceMarking n fN b ≫
      (independentCyclicNormalizationBaseIso n f).hom.hom.hom.hom).left ≫
        pullback.fst universalGroup.hom (aN ≫ levelFour.hom) =
      (independentCyclicSourceMarking n f b ≫
        (auxiliarySchemeNormalizationGroupIso a).inv.hom.hom.hom).left ≫
          pullback.fst universalGroup.hom (aN ≫ levelFour.hom)
    rw [Over.comp_left, Over.comp_left, Category.assoc,
      independentCyclicNormalizationBaseIso_fst, independentCyclicSourceMarking_fst,
      independentCyclicNormalizedPoint_value, Category.assoc]
  · exact (independentCyclicSourceMarking n fN b ≫
      (independentCyclicNormalizationBaseIso n f).hom.hom.hom.hom).w.trans
        (independentCyclicSourceMarking n f b ≫
          (auxiliarySchemeNormalizationGroupIso a).inv.hom.hom.hom).w.symm

/-- The normalization isomorphism identifies every normalized cyclic section with its original. -/
theorem independentCyclicNormalizationGroupIso_marking (b : Multiplicative (ZMod n)) :
    independentCyclicSourceMarking n fN b ≫
      (independentCyclicNormalizationGroupIso n f).hom.hom.hom.hom =
        independentCyclicSourceMarking n f b := by
  rw [independentCyclicNormalizationGroupIso_def]
  change independentCyclicSourceMarking n fN b ≫
    (independentCyclicNormalizationBaseIso n f).hom.hom.hom.hom ≫
      (auxiliarySchemeNormalizationGroupIso a).hom.hom.hom.hom = _
  rw [← Category.assoc, independentCyclicNormalizationBaseIso_marking, Category.assoc]
  let e := (CommGrp.forget _).mapIso (auxiliarySchemeNormalizationGroupIso a)
  change independentCyclicSourceMarking n f b ≫ e.inv ≫ e.hom = _
  rw [e.inv_hom_id]
  exact Category.comp_id _

end FLT.Mazur.UniversalWeierstrass

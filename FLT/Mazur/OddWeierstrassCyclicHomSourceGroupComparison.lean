/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module
public import FLT.Mazur.OddWeierstrassCyclicHomSourcePullback
public import FLT.Mazur.GeneralizedCurveCyclicMarkingBaseChange
public import FLT.Mazur.GroupSchemeBaseChangeComposition
public import FLT.Mazur.OddWeierstrassAuxiliarySchemeMarking
/-!
# Source change of the original full cyclic group family
The comparison between iterated and direct pullback retains the original
coefficient map and the universal family projection.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
open IntegralWeierstrassParameter (oddChartEquation oddChart_discriminant)
open WeierstrassIntegralChart GeneralizedEllipticCurve
open MonoidalCategory MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n] {T U : Scheme}
  (f : T ⟶ (cyclicHomAuxiliaryScheme n).left) (k : U ⟶ T)
local notation "a" => cyclicHomAuxiliaryPoint n f
local notation "b" => cyclicHomAuxiliaryPoint n (k ≫ f)
local notation "G" => integralCurveGroup oddChartEquation oddChart_discriminant
/-- The two constructions use exactly the same original coefficient map. -/
theorem cyclicHomSourceGroup_base :
    k ≫ (a ≫ levelThree.hom) = b ≫ levelThree.hom := by
  simp only [cyclicHomAuxiliaryPoint, Category.assoc]
/-- Pulling back an original family gives the original family at the pulled-back full point. -/
irreducible_def cyclicHomSourceGroupIso :
    (Over.pullback k).mapCommGrp.obj (auxiliarySchemeGroup a) ≅ auxiliarySchemeGroup b :=
  (GroupSchemeBaseChange.compIso k (a ≫ levelThree.hom) G).symm ≪≫
    GroupSchemeBaseChange.congrIso (cyclicHomSourceGroup_base n f k) G
/-- The source comparison retains the exact universal projection. -/
@[reassoc] theorem cyclicHomSourceGroupIso_fst :
    (cyclicHomSourceGroupIso n f k).hom.hom.hom.hom.left ≫
      pullback.fst universalGroup.hom (b ≫ levelThree.hom) =
        pullback.fst (auxiliarySchemeGroup a).X.hom k ≫
          pullback.fst universalGroup.hom (a ≫ levelThree.hom) := by
  rw [cyclicHomSourceGroupIso_def]
  change (_ ≫ _) ≫ _ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z ↦
      (GroupSchemeBaseChange.compIso k (a ≫ levelThree.hom) G).inv.hom.hom.hom.left ≫ z)
        (GroupSchemeBaseChange.congrIso_hom_fst (cyclicHomSourceGroup_base n f k) G)).trans
          (GroupSchemeBaseChange.compIso_inv_fst k (a ≫ levelThree.hom) G))
/-- The source comparison carries each pulled original section to the new source section. -/
theorem cyclicHomSourceGroupIso_marking (c : Multiplicative (ZMod n)) :
    pullCyclicMarking (E := cyclicHomSourceCurve n f)
      k (cyclicHomSourceMarking n f) c ≫
      (cyclicHomSourceGroupIso n f k).hom.hom.hom.hom =
        cyclicHomSourceMarking n (k ≫ f) c := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (pullCyclicMarking (E := cyclicHomSourceCurve n f)
      k (cyclicHomSourceMarking n f) c ≫
      (cyclicHomSourceGroupIso n f k).hom.hom.hom.hom).left ≫
        pullback.fst universalGroup.hom (b ≫ levelThree.hom) =
      (cyclicHomSourceMarking n (k ≫ f) c).left ≫
        pullback.fst universalGroup.hom (b ≫ levelThree.hom)
    rw [Over.comp_left, Category.assoc, cyclicHomSourceGroupIso_fst,
      ← Category.assoc]
    change ((pullCyclicMarking (E := cyclicHomSourceCurve n f)
      k (cyclicHomSourceMarking n f) c).left ≫
      pullback.fst (cyclicHomSourceCurve n f).group.hom k) ≫ _ = _
    rw [pullCyclicMarking_fst]
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun z ↦ k ≫ z) (cyclicHomSourceMarking_fst n f c)).trans
        ((Category.assoc _ _ _).symm.trans
          (cyclicHomSourceMarking_fst n (k ≫ f) c).symm))
  · exact (pullCyclicMarking (E := cyclicHomSourceCurve n f)
      k (cyclicHomSourceMarking n f) c ≫
      (cyclicHomSourceGroupIso n f k).hom.hom.hom.hom).w.trans
        (cyclicHomSourceMarking n (k ≫ f) c).w.symm

/-- Source comparison also retains every independent auxiliary label. -/
theorem cyclicHomSourceGroupIso_auxiliary (c : Labels 3) :
    GroupSectionBaseChange.pullSection k (auxiliarySchemeMarking a c) ≫
      (cyclicHomSourceGroupIso n f k).hom.hom.hom.hom = auxiliarySchemeMarking b c := by
  apply auxiliarySchemeMarking_ext
  rw [Over.comp_left, Category.assoc, cyclicHomSourceGroupIso_fst, ← Category.assoc,
    GroupSectionBaseChange.section_fst, Category.assoc, auxiliarySchemeMarking_fst]
  simp only [cyclicHomAuxiliaryPoint, Category.assoc]

end FLT.Mazur.OddWeierstrassParameter

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module
public import FLT.Mazur.IndependentCyclicSourceModuli
public import FLT.Mazur.GeneralizedCurveCyclicMarkingBaseChange
public import FLT.Mazur.GroupSchemeBaseChangeComposition
/-!
# Source change of the original full cyclic group family
The comparison between iterated and direct pullback retains the original
coefficient map and the universal family projection.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
open WeierstrassIntegralChart GeneralizedEllipticCurve
open MonoidalCategory MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n] {T U : Scheme}
  (f : T ⟶ (independentCyclicAuxiliaryScheme n).left) (k : U ⟶ T)
local notation "a" => independentCyclicAuxiliaryPoint n f
local notation "b" => independentCyclicAuxiliaryPoint n (k ≫ f)
local notation "G" => integralCurveGroup smoothEquation smoothEquation_discriminant
/-- The two constructions use exactly the same original coefficient map. -/
theorem independentCyclicSourceGroup_base :
    k ≫ (a ≫ levelFour.hom) = b ≫ levelFour.hom := by
  simp only [independentCyclicAuxiliaryPoint, Category.assoc]
/-- Pulling back an original family gives the original family at the pulled-back full point. -/
irreducible_def independentCyclicSourceGroupIso :
    (Over.pullback k).mapCommGrp.obj (auxiliarySchemeGroup a) ≅ auxiliarySchemeGroup b :=
  (GroupSchemeBaseChange.compIso k (a ≫ levelFour.hom) G).symm ≪≫
    GroupSchemeBaseChange.congrIso (independentCyclicSourceGroup_base n f k) G
/-- The source comparison retains the exact universal projection. -/
@[reassoc] theorem independentCyclicSourceGroupIso_fst :
    (independentCyclicSourceGroupIso n f k).hom.hom.hom.hom.left ≫
      pullback.fst universalGroup.hom (b ≫ levelFour.hom) =
        pullback.fst (auxiliarySchemeGroup a).X.hom k ≫
          pullback.fst universalGroup.hom (a ≫ levelFour.hom) := by
  rw [independentCyclicSourceGroupIso_def]
  change (_ ≫ _) ≫ _ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z ↦
      (GroupSchemeBaseChange.compIso k (a ≫ levelFour.hom) G).inv.hom.hom.hom.left ≫ z)
        (GroupSchemeBaseChange.congrIso_hom_fst (independentCyclicSourceGroup_base n f k) G)).trans
          (GroupSchemeBaseChange.compIso_inv_fst k (a ≫ levelFour.hom) G))
/-- The source comparison carries each pulled original section to the new source section. -/
theorem independentCyclicSourceGroupIso_marking (c : Multiplicative (ZMod n)) :
    pullCyclicMarking (E := independentCyclicSourceCurve n f)
      k (independentCyclicSourceMarking n f) c ≫
      (independentCyclicSourceGroupIso n f k).hom.hom.hom.hom =
        independentCyclicSourceMarking n (k ≫ f) c := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (pullCyclicMarking (E := independentCyclicSourceCurve n f)
      k (independentCyclicSourceMarking n f) c ≫
      (independentCyclicSourceGroupIso n f k).hom.hom.hom.hom).left ≫
        pullback.fst universalGroup.hom (b ≫ levelFour.hom) =
      (independentCyclicSourceMarking n (k ≫ f) c).left ≫
        pullback.fst universalGroup.hom (b ≫ levelFour.hom)
    rw [Over.comp_left, Category.assoc, independentCyclicSourceGroupIso_fst,
      ← Category.assoc]
    change ((pullCyclicMarking (E := independentCyclicSourceCurve n f)
      k (independentCyclicSourceMarking n f) c).left ≫
      pullback.fst (independentCyclicSourceCurve n f).group.hom k) ≫ _ = _
    rw [pullCyclicMarking_fst]
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun z ↦ k ≫ z) (independentCyclicSourceMarking_fst n f c)).trans
        ((Category.assoc _ _ _).symm.trans
          (independentCyclicSourceMarking_fst n (k ≫ f) c).symm))
  · exact (pullCyclicMarking (E := independentCyclicSourceCurve n f)
      k (independentCyclicSourceMarking n f) c ≫
      (independentCyclicSourceGroupIso n f k).hom.hom.hom.hom).w.trans
        (independentCyclicSourceMarking n (k ≫ f) c).w.symm
end FLT.Mazur.UniversalWeierstrass

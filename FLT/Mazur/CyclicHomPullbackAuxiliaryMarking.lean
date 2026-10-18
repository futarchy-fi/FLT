/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicHomSourcePullback
public import FLT.Mazur.CyclicHomSubgroupPullbackMarking

/-!
# Auxiliary markings under source and subgroup pullback

The full source comparison preserves the independent auxiliary frame under
arbitrary base change. The actual subgroup comparison has the same property.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.UniversalWeierstrass
open AuxiliaryLevel GeneralizedEllipticCurve GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T U : Scheme}
  (f : T ⟶ (cyclicHomAuxiliaryScheme n).left) (k : U ⟶ T)

/-- Every independent auxiliary label survives the full source pullback comparison. -/
theorem cyclicHomSourcePullbackIso_auxiliary (i : Labels 4) :
    auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n (k ≫ f)) i ≫
      (cyclicHomSourcePullbackIso n f k).hom.group =
        pullSection k (auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) i) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · change (auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n (k ≫ f)) i).left ≫
        (cyclicHomSourcePullbackIso n f k).hom.group.left ≫
          pullback.fst (cyclicHomSourceCurve n f).group.hom k ≫
            pullback.fst universalGroup.hom (cyclicHomAuxiliaryPoint n f ≫ levelFour.hom) =
          (pullSection k (auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) i)).left ≫
            pullback.fst (cyclicHomSourceCurve n f).group.hom k ≫
              pullback.fst universalGroup.hom (cyclicHomAuxiliaryPoint n f ≫ levelFour.hom)
      rw [cyclicHomSourcePullbackIso_group_fst, auxiliarySchemeMarking_fst]
      have hs := section_fst k (auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) i)
      change (pullSection k (auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) i)).left ≫
        pullback.fst (cyclicHomSourceCurve n f).group.hom k =
          k ≫ (auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) i).left at hs
      rw [← Category.assoc _ (pullback.fst (cyclicHomSourceCurve n f).group.hom k), hs,
        Category.assoc, auxiliarySchemeMarking_fst]
      simp only [cyclicHomAuxiliaryPoint, Category.assoc]
    · have hw := (auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n (k ≫ f)) i ≫
        (cyclicHomSourcePullbackIso n f k).hom.group).w.trans
          (pullSection k (auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) i)).w.symm
      change (_ ≫ pullback.fst (cyclicHomSourceCurve n f).group.hom k) ≫
        (cyclicHomSourceCurve n f).group.hom =
          (_ ≫ pullback.fst (cyclicHomSourceCurve n f).group.hom k) ≫
            (cyclicHomSourceCurve n f).group.hom
      simpa only [Category.assoc, pullback.condition] using! congrArg (· ≫ k) hw
  · exact Over.w _ |>.trans (Over.w _).symm

/-- The actual subgroup pullback comparison retains the same auxiliary frame. -/
theorem cyclicHomSubgroupPullbackIso_auxiliary
    (h : cyclicHomMultiplicationEquation n f = 0) (i : Labels 4) :
    auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n (k ≫ f)) i ≫
      (cyclicHomSubgroupPullbackIso n f k h).curve.hom.group =
        pullSection k (auxiliarySchemeMarking (cyclicHomAuxiliaryPoint n f) i) := by
  rw [cyclicHomSubgroupPullbackIso_curve]
  exact cyclicHomSourcePullbackIso_auxiliary n f k i

end FLT.Mazur.UniversalWeierstrass

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicHomSourceDivisor
public import FLT.Mazur.GeneralizedCurveBaseChangeCompEq

/-!
# The unrestricted cyclic source commutes with parameter pullback

The comparison is an isomorphism of full generalized elliptic curves. It
retains the original coefficient curve and all cyclic labels, including
coincident labels over nonreduced bases.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.UniversalWeierstrass
open AuxiliaryLevel GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T U : Scheme}
  (f : T ⟶ (cyclicHomAuxiliaryScheme n).left) (k : U ⟶ T)

/-- The coefficient map commutes with arbitrary parameter change. -/
theorem cyclicHomSourceBase_comp :
    cyclicHomAuxiliaryPoint n (k ≫ f) ≫ levelFour.hom =
      k ≫ (cyclicHomAuxiliaryPoint n f ≫ levelFour.hom) := by
  simp only [cyclicHomAuxiliaryPoint, Category.assoc]

/-- Direct and iterated cyclic source families agree as full curve objects. -/
def cyclicHomSourcePullbackIso :
    cyclicHomSourceCurve n (k ≫ f) ≅ (cyclicHomSourceCurve n f).baseChange k :=
  universalCurve.baseChangeCompEqIso (cyclicHomAuxiliaryPoint n f ≫ levelFour.hom) k
    (cyclicHomAuxiliaryPoint n (k ≫ f) ≫ levelFour.hom) (cyclicHomSourceBase_comp n f k)

/-- The curve comparison retains the original universal-curve projection. -/
@[reassoc] theorem cyclicHomSourcePullbackIso_curve_fst :
    (cyclicHomSourcePullbackIso n f k).hom.curve.left ≫
      pullback.fst (cyclicHomSourceCurve n f).curve.hom k ≫
        pullback.fst universalCurve.curve.hom
          (cyclicHomAuxiliaryPoint n f ≫ levelFour.hom) =
      pullback.fst universalCurve.curve.hom
        (cyclicHomAuxiliaryPoint n (k ≫ f) ≫ levelFour.hom) :=
  universalCurve.baseChangeCompEqIso_curve_fst _ _ _ (cyclicHomSourceBase_comp n f k)

/-- The group comparison retains the original universal-group projection. -/
@[reassoc] theorem cyclicHomSourcePullbackIso_group_fst :
    (cyclicHomSourcePullbackIso n f k).hom.group.left ≫
      pullback.fst (cyclicHomSourceCurve n f).group.hom k ≫
        pullback.fst universalGroup.hom
          (cyclicHomAuxiliaryPoint n f ≫ levelFour.hom) =
      pullback.fst universalGroup.hom
        (cyclicHomAuxiliaryPoint n (k ≫ f) ≫ levelFour.hom) :=
  universalCurve.baseChangeCompEqIso_group_fst _ _ _ (cyclicHomSourceBase_comp n f k)

/-- Every cyclic label is preserved by the full source-family comparison. -/
theorem cyclicHomSourcePullbackIso_marking (i : Multiplicative (ZMod n)) :
    cyclicHomSourceMarking n (k ≫ f) i ≫ (cyclicHomSourcePullbackIso n f k).hom.group =
      pullCyclicMarking k (cyclicHomSourceMarking n f) i := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [Over.comp_left, Category.assoc,
        cyclicHomSourcePullbackIso_group_fst, cyclicHomSourceMarking_fst,
        pullCyclicMarking_fst_assoc, cyclicHomSourceMarking_fst]
    · have hw := (cyclicHomSourceMarking n (k ≫ f) i ≫
        (cyclicHomSourcePullbackIso n f k).hom.group).w.trans
          (pullCyclicMarking k (cyclicHomSourceMarking n f) i).w.symm
      change (_ ≫ pullback.fst (cyclicHomSourceCurve n f).group.hom k) ≫
        (cyclicHomSourceCurve n f).group.hom =
          (_ ≫ pullback.fst (cyclicHomSourceCurve n f).group.hom k) ≫
            (cyclicHomSourceCurve n f).group.hom
      simpa only [Category.assoc, pullback.condition] using! congrArg (· ≫ k) hw
  · exact Over.w _ |>.trans (Over.w _).symm

end FLT.Mazur.UniversalWeierstrass

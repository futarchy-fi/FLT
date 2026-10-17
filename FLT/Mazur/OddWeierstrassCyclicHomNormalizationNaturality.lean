/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassAuxiliarySchemeNormalizationNaturality
public import FLT.Mazur.OddWeierstrassCyclicHomPointExt

/-!
# Full cyclic normalization is natural on all test schemes

Every full label is normalized by the same actual family comparison. The
auxiliary and cyclic value equations prove compatibility with every source
morphism, including nonaffine and nonreduced sources.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj
namespace FLT.Mazur.OddWeierstrassParameter
open AuxiliaryLevel
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (n : ℕ) [NeZero n] {T U : Scheme} (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)

/-- Every original cyclic value lies over the original auxiliary coefficient parameter. -/
theorem cyclicHomValue_base (c : Multiplicative (ZMod n)) :
    (f ≫ (cyclicHomParameter n ≫ value universalGroup (Multiplicative (ZMod n)) c).left) ≫
        universalGroup.hom = cyclicHomAuxiliaryPoint n f ≫ levelThree.hom := by
  rw [Category.assoc, (cyclicHomParameter n ≫
    value universalGroup (Multiplicative (ZMod n)) c).w]
  exact ((Category.assoc _ _ _).trans
    (congrArg (fun z ↦ f ≫ z) (cyclicHomAuxiliary n).w)).symm

/-- Every full label is the actual normalization of its original universal value. -/
theorem cyclicHomNormalizedPoint_value_normalize (c : Multiplicative (ZMod n)) :
    cyclicHomNormalizedPoint n f ≫
        (cyclicHomParameter n ≫ value universalGroup (Multiplicative (ZMod n)) c).left =
      auxiliarySchemeNormalizedValue (cyclicHomAuxiliaryPoint n f)
        (f ≫ (cyclicHomParameter n ≫ value universalGroup (Multiplicative (ZMod n)) c).left)
        (cyclicHomValue_base n f c) := by
  have hl : pullback.lift
      (f ≫ (cyclicHomParameter n ≫ value universalGroup (Multiplicative (ZMod n)) c).left)
      (𝟙 T) ((cyclicHomValue_base n f c).trans (Category.id_comp _).symm) =
    (cyclicHomSourceMarking n f c).left := by
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans (cyclicHomSourceMarking_fst n f c).symm
    · exact (pullback.lift_snd _ _ _).trans (cyclicHomSourceMarking n f c).w.symm
  rw [cyclicHomNormalizedPoint_value, auxiliarySchemeNormalizedValue, hl]

/-- Independent normalization of every full cyclic point commutes with arbitrary source maps. -/
theorem cyclicHomNormalizedPoint_natural (k : U ⟶ T) :
    cyclicHomNormalizedPoint n (k ≫ f) = k ≫ cyclicHomNormalizedPoint n f := by
  apply cyclicHomPoint_ext n
  · rw [Category.assoc, cyclicHomNormalizedPoint_auxiliary,
      cyclicHomNormalizedPoint_auxiliary]
    simpa only [cyclicHomAuxiliaryPoint, Category.assoc] using
      auxiliarySchemeNormalizedPoint_natural (cyclicHomAuxiliaryPoint n f) k
  · intro c
    rw [Category.assoc, cyclicHomNormalizedPoint_value_normalize,
      cyclicHomNormalizedPoint_value_normalize]
    exact auxiliarySchemeNormalizedValue_natural_of_eq _ _ (cyclicHomValue_base n f c)
      k _ _ (cyclicHomValue_base n (k ≫ f) c)
      (Category.assoc _ _ _) (Category.assoc _ _ _)

end FLT.Mazur.OddWeierstrassParameter

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassAuxiliarySchemeMarking

/-!
# Faithful auxiliary markings after restricting the test scheme

Precomposition retains the whole marking as a group homomorphism into relative
points of the original family. It is faithful on every nonempty test scheme.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {T U : Scheme} (f : T ⟶ levelThree.left) (k : U ⟶ T)

/-- Restrict the marking as relative points of the unchanged original group family. -/
def auxiliaryRestrictedMarking :
    Labels 3 →* (Over.mk k ⟶ (auxiliarySchemeGroup f).X) :=
  ((yonedaMonObj (auxiliarySchemeGroup f).X).map
    (Over.homMk k (Category.comp_id k)).op).hom.comp (auxiliarySchemeMarking f)

/-- Restriction is the actual composition of original section morphisms. -/
theorem auxiliaryRestrictedMarking_left (a : Labels 3) :
    (auxiliaryRestrictedMarking f k a).left = k ≫ (auxiliarySchemeMarking f a).left := rfl

/-- Any nonempty test scheme still detects distinct original auxiliary labels. -/
theorem auxiliaryRestrictedMarking_injective [Nonempty U] :
    Function.Injective (auxiliaryRestrictedMarking f k) := by
  intro a b hab
  apply auxiliarySchemeMarking_injective (k ≫ f)
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (auxiliarySchemeMarking (k ≫ f) a).left ≫
        pullback.fst universalGroup.hom ((k ≫ f) ≫ levelThree.hom) =
      (auxiliarySchemeMarking (k ≫ f) b).left ≫
        pullback.fst universalGroup.hom ((k ≫ f) ≫ levelThree.hom)
    rw [auxiliarySchemeMarking_fst, auxiliarySchemeMarking_fst]
    have h := congrArg (fun z => z.left ≫
      pullback.fst universalGroup.hom (f ≫ levelThree.hom)) hab
    simpa only [auxiliaryRestrictedMarking_left, Category.assoc,
      auxiliarySchemeMarking_fst] using h
  · exact (auxiliarySchemeMarking (k ≫ f) a).w.trans
      (auxiliarySchemeMarking (k ≫ f) b).w.symm

end FLT.Mazur.OddWeierstrassParameter

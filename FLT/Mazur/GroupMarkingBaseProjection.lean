/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroupMarkingBaseChange

/-!
# Full markings projected through the original pullback adjunction

The inverse group-valued adjunction descends complete label homomorphisms to
the original group on the same test scheme, retaining every projected map.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.GroupMarkingBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (g : T ⟶ S) (G : Over S) [MonObj G] (U : Over T)
  {A : Type} [Monoid A]

/-- Project the entire label homomorphism using the actual inverse adjunction. -/
def projectMarking (m : A →* (U ⟶ (Over.pullback g).obj G)) :
    A →* ((Over.map g).obj U ⟶ G) :=
  (pointsMulEquiv g G U).symm.toMonoidHom.comp m

/-- Every projected label is the original pullback projection. -/
theorem projectMarking_left (m : A →* (U ⟶ (Over.pullback g).obj G)) (a : A) :
    (projectMarking g G U m a).left = (m a).left ≫ pullback.fst G.hom g := by
  have h := pointsMulEquiv_fst g G U ((pointsMulEquiv g G U).symm (m a))
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

/-- Lifting the projection restores the full original marking. -/
theorem marking_projectMarking (m : A →* (U ⟶ (Over.pullback g).obj G)) :
    marking g G U (projectMarking g G U m) = m := by
  apply MonoidHom.ext
  intro a
  exact (pointsMulEquiv g G U).apply_symm_apply (m a)

/-- Projection detects equality of the full marking. -/
theorem projectMarking_injective_iff (m : A →* (U ⟶ (Over.pullback g).obj G)) :
    Function.Injective (projectMarking g G U m) ↔ Function.Injective m :=
  (pointsMulEquiv g G U).symm.injective.of_comp_iff m

end FLT.Mazur.GroupMarkingBaseChange

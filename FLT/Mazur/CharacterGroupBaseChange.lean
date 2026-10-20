/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CharacterScalarBialgebra
public import FLT.Mazur.CharacterSchemeBaseChange
public import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# Arithmetic character comparisons preserve the group law

The tensor spectrum comparison and the bialgebra coordinate map identify the
actual base change group law with the character group law over the new ring.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct CategoryTheory.Obj

namespace FLT.Mazur.CharacterGroupBaseChange

open CharacterAlgebraScalarExtension CharacterSchemeBaseChange

universe u
variable (R A M : Type u) [CommRing R] [CommRing A] [Algebra R A] [AddCommMonoid M]

instance modelMonObj : MonObj (model R M) :=
  inferInstanceAs (MonObj ((Spec (.of (AddMonoidAlgebra R M))).asOver (Spec (.of R))))

/-- The inverse comparison is the composite of the two standard group morphisms. -/
theorem inverse_factorization :
    (overIso R A M).inv =
      (pullbackSymmetry _ _ ≪≫ pullbackSpecIso' R A (AddMonoidAlgebra R M)).hom.asOver
        (Spec (.of A)) ≫
      ((bialgSpec (.of A)).map (CommBialgCat.ofHom
        (CharacterScalarBialgebra.inverse R A M)).op).hom := by
  apply Over.OverMorphism.ext
  rfl

instance inverse_isMonHom : IsMonHom (overIso R A M).inv := by
  rw [inverse_factorization]
  infer_instance

instance comparison_isMonHom : IsMonHom (overIso R A M).hom := by
  let _ : IsMonHom (overIso R A M).symm.hom := inverse_isMonHom R A M
  exact inferInstanceAs (IsMonHom (overIso R A M).symm.inv)

end FLT.Mazur.CharacterGroupBaseChange

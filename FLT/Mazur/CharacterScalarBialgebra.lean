/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CharacterAlgebraScalarExtension
public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import Mathlib.RingTheory.Bialgebra.TensorProduct

/-!
# The coalgebra law in arithmetic character coordinates

The inverse scalar tensor equivalence preserves counit and comultiplication.
Thus changing coefficients preserves the group law, including over nonreduced rings.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.CharacterScalarBialgebra

open CharacterAlgebraScalarExtension

variable (R A M : Type*) [CommRing R] [CommRing A] [Algebra R A] [AddCommMonoid M]

omit [AddCommMonoid M] in
/-- The tensor representative of a character has the diagonal comultiplication. -/
theorem comul_character (m : M) (a : A) :
    Coalgebra.comul (R := A) (a ⊗ₜ[R] AddMonoidAlgebra.single m (1 : R)) =
      (1 ⊗ₜ[R] AddMonoidAlgebra.single m (1 : R)) ⊗ₜ[A]
        (a ⊗ₜ[R] AddMonoidAlgebra.single m (1 : R)) := by
  simp [TensorProduct.comul_tmul]

/-- The inverse coordinate comparison as a genuine bialgebra homomorphism. -/
def inverse : AddMonoidAlgebra A M →ₐc[A] A ⊗[R] AddMonoidAlgebra R M where
  __ := (equivalence R A M).symm.toAlgHom
  __ := (equivalence R A M).symm.toLinearMap
  counit_comp := by
    apply AddMonoidAlgebra.lhom_ext'
    intro m
    ext
    simp [equivalence_symm_single]
  map_comp_comul := by
    apply AddMonoidAlgebra.lhom_ext'
    intro m
    ext
    simp [equivalence_symm_single]

/-- The bialgebra map is exactly the previously specified tensor coordinate map. -/
theorem inverse_toAlgHom : (inverse R A M).toAlgHom = (equivalence R A M).symm.toAlgHom := rfl

end FLT.Mazur.CharacterScalarBialgebra

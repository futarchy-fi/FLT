/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DiagonalizableCobarAlgebra

/-!
# Algebra coordinates on the product of diagonalizable tests

The tensor equivalence is an algebra equivalence. Its two inclusions are the
original character projections and its comultiplication is the diagonal map.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.DiagonalizableCobar

open scoped TensorProduct

variable (R G : Type*) [CommRing R] [AddCommMonoid G]

/-- Multiply the two independent character inclusions. -/
def productMap : AddMonoidAlgebra R G ⊗[R] AddMonoidAlgebra R G →ₐ[R]
    AddMonoidAlgebra R (G × G) :=
  Algebra.TensorProduct.lift (firstMap R G) (secondMap R G) (fun _ _ => .all ..)

/-- The actual product algebra map is the full coefficient tensor equivalence. -/
theorem productMap_eq_tensorEquiv (q : AddMonoidAlgebra R G ⊗[R] AddMonoidAlgebra R G) :
    productMap R G q = AddMonoidAlgebra.tensorEquiv R q := by
  induction q using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x y =>
    induction x using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add x z hx hz => simp only [TensorProduct.add_tmul, map_add, hx, hz]
    | single a r =>
      induction y using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
      | single b s => simp [productMap, firstMap, secondMap]

/-- The full tensor algebra is the full product-character algebra. -/
def productEquiv : AddMonoidAlgebra R G ⊗[R] AddMonoidAlgebra R G ≃ₐ[R]
    AddMonoidAlgebra R (G × G) :=
  AlgEquiv.ofBijective (productMap R G) (by
    have he : (productMap R G : _ → _) = AddMonoidAlgebra.tensorEquiv R :=
      funext (productMap_eq_tensorEquiv R G)
    rw [he]
    exact (AddMonoidAlgebra.tensorEquiv R).bijective)

/-- The first projection retains its original character inclusion. -/
theorem productEquiv_includeLeft :
    (productEquiv R G).toAlgHom.comp Algebra.TensorProduct.includeLeft = firstMap R G := by
  ext x
  simp [productEquiv, productMap]

/-- The second projection retains its original character inclusion. -/
theorem productEquiv_includeRight :
    (productEquiv R G).toAlgHom.comp Algebra.TensorProduct.includeRight = secondMap R G := by
  ext x
  simp [productEquiv, productMap]

/-- The actual Hopf comultiplication becomes precisely the original diagonal character map. -/
theorem productEquiv_comul :
    (productEquiv R G).toAlgHom.comp (Bialgebra.comulAlgHom R (AddMonoidAlgebra R G)) =
      diagonalMap R G := by
  apply AlgHom.ext
  intro q
  exact (productMap_eq_tensorEquiv R G _).trans (diagonalMap_comul R G q).symm

end FLT.Mazur.DiagonalizableCobar

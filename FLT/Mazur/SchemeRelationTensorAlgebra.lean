/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationTensorCoordinates

/-!
# Original base scalars in relation tensor coordinates

The multiplicative coordinate comparison respects the structural R-algebras.
This permits tensoring the actual comparison on a further independent base.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
namespace FLT.Mazur.SchemeRelationTensor
open Approximation
universe u
set_option backward.isDefEq.respectTransparency false
variable {R : Type u} [CommRing R] {A V Z : Over (Spec (.of R))}
  [IsAffine A.left] [IsAffine V.left]
  (β : A ⟶ V) (p q : Z ⟶ A) (j : Z ⟶ prod A V)
  (hq : j ≫ prod.fst = q) (hp : j ≫ prod.snd = p ≫ β) [IsIso j.left]
/-- The algebra induced by the original structural morphism. -/
local instance algebraSource : Algebra R Γ(A.left, ⊤) := affineBaseSectionAlgebra A.hom
/-- The algebra induced by the original structural morphism. -/
local instance algebraBase : Algebra R Γ(V.left, ⊤) := affineBaseSectionAlgebra V.hom
/-- The algebra induced by the original structural morphism. -/
local instance algebraRelation : Algebra R Γ(Z.left, ⊤) := affineBaseSectionAlgebra Z.hom

include hp hq in
/-- The tensor coordinates preserve the original R-coefficients. -/
theorem coordinates_scalar (r : R) :
    coordinates j (algebraMap R (Γ(V.left, ⊤) ⊗[R] Γ(A.left, ⊤)) r) =
      algebraMap R Γ(Z.left, ⊤) r := by
  rw [Algebra.TensorProduct.algebraMap_apply, coordinates_tmul β p q j hq hp,
    map_one, one_mul]
  exact (affineBaseSectionHom Z.hom V.hom (p ≫ β).left (p ≫ β).w).commutes r

/-- Multiplicative relation coordinates with their original R-algebra structure retained. -/
def coordinatesAlgEquiv : Γ(V.left, ⊤) ⊗[R] Γ(A.left, ⊤) ≃ₐ[R] Γ(Z.left, ⊤) :=
  { coordinates j with commutes' := coordinates_scalar β p q j hq hp }

/-- Extending the actual relation comparison keeps a further independent base coordinate. -/
def extendedCoordinates :
    Γ(V.left, ⊤) ⊗[R] (Γ(V.left, ⊤) ⊗[R] Γ(A.left, ⊤)) ≃ₐ[R]
      Γ(V.left, ⊤) ⊗[R] Γ(Z.left, ⊤) :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : Γ(V.left, ⊤) ≃ₐ[R] Γ(V.left, ⊤))
    (coordinatesAlgEquiv β p q j hq hp)

/-- Tensor extension changes only the relation coefficient, retaining its independent scalar. -/
theorem extendedCoordinates_tmul (s : Γ(V.left, ⊤))
    (z : Γ(V.left, ⊤) ⊗[R] Γ(A.left, ⊤)) :
    extendedCoordinates β p q j hq hp (s ⊗ₜ[R] z) = s ⊗ₜ[R] coordinates j z := rfl

end FLT.Mazur.SchemeRelationTensor

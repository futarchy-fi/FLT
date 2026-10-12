/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationTensorCoordinates
public import FLT.Mazur.AffineAlgebraDescentCoaction

/-!
# The coaction counit from the original relation identity

The geometric identity evaluates the two independent tensor coefficients by
scalar multiplication. Its first endpoint equation proves the counit law.
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
local instance counitSourceAlgebra : Algebra R Γ(A.left, ⊤) := affineBaseSectionAlgebra A.hom
/-- The algebra induced by the original structural morphism. -/
local instance counitBaseAlgebra : Algebra R Γ(V.left, ⊤) := affineBaseSectionAlgebra V.hom
variable (r : A ⟶ Z) (hrp : r ≫ p = 𝟙 A) (hrq : r ≫ q = 𝟙 A)

include hq hp hrp hrq in
/-- The original identity pulls literal tensor coordinates back by scalar multiplication. -/
theorem identity_coordinates (z : Γ(V.left, ⊤) ⊗[R] Γ(A.left, ⊤)) :
    let _ := coefficientAlgebra β
    let _ := coefficientTower β
    r.left.appTop (coordinates j z) =
      TensorProduct.lift (Algebra.lsmul R R Γ(A.left, ⊤)
        (A := Γ(V.left, ⊤))).toLinearMap z := by
  let _ := coefficientAlgebra β
  let _ := coefficientTower β
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s b =>
    rw [coordinates_tmul β p q j hq hp, map_mul]
    change (r ≫ q).left.appTop b * (r ≫ p ≫ β).left.appTop s =
      (β.left.appTop s) * b
    rw [hrq, ← Category.assoc, hrp, Category.id_comp]
    change b * β.left.appTop s = β.left.appTop s * b
    exact mul_comm _ _

include hq hp hrp hrq in
/-- Reflexivity of the original relation proves the algebra coaction counit. -/
theorem coaction_counit (b : Γ(A.left, ⊤)) :
    let _ := coefficientAlgebra β
    let _ := coefficientTower β
    TensorProduct.lift (Algebra.lsmul R R Γ(A.left, ⊤)
      (A := Γ(V.left, ⊤))).toLinearMap (coaction β p q j hq hp b) = b := by
  let _ := coefficientAlgebra β
  let _ := coefficientTower β
  dsimp only
  rw [← identity_coordinates β p q j hq hp r hrp hrq, coaction_apply, coordinates_source]
  change (r ≫ p).left.appTop b = b
  rw [hrp]
  rfl

end FLT.Mazur.SchemeRelationTensor

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationTensorAlgebra
public import FLT.Mazur.AffineAlgebraDescentCoaction

/-!
# The coaction cocycle from actual geometric composition

Tensor extension identifies the original three-coordinate envelope. The two
coaction composites are the original first-arrow and composite pullbacks.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
namespace FLT.Mazur.SchemeRelationTensor
open Approximation
universe u
set_option backward.isDefEq.respectTransparency false
variable {R : Type u} [CommRing R] {A V Z C : Over (Spec (.of R))}
  [IsAffine A.left] [IsAffine V.left] [IsAffine Z.left]
  (β : A ⟶ V) (p q : Z ⟶ A) (j : Z ⟶ prod A V)
  (hq : j ≫ prod.fst = q) (hp : j ≫ prod.snd = p ≫ β) [IsIso j.left]
  (a b m : C ⟶ Z) (l : C ⟶ prod Z V) [IsIso l.left]
  (hlb : l ≫ prod.fst = b) (hla : l ≫ prod.snd = a ≫ p ≫ β)
  (hab : a ≫ q = b ≫ p) (hmp : m ≫ p = a ≫ p) (hmq : m ≫ q = b ≫ q)
/-- The source coefficients use the original structural map. -/
local instance cocycleSource : Algebra R Γ(A.left, ⊤) := affineBaseSectionAlgebra A.hom
/-- The independent base coefficients use the original structural map. -/
local instance cocycleBase : Algebra R Γ(V.left, ⊤) := affineBaseSectionAlgebra V.hom
/-- The relation coefficients use the original structural map. -/
local instance cocycleRelation : Algebra R Γ(Z.left, ⊤) := affineBaseSectionAlgebra Z.hom

/-- The actual three-coordinate envelope, as a multiplicative tensor equivalence. -/
def tripleCoordinates :
    Γ(V.left, ⊤) ⊗[R] (Γ(V.left, ⊤) ⊗[R] Γ(A.left, ⊤)) ≃+* Γ(C.left, ⊤) :=
  (extendedCoordinates β p q j hq hp).toRingEquiv.trans (coordinates l)

include hlb hla in
/-- The outer scalar and the complete second arrow remain independent. -/
theorem tripleCoordinates_tmul (s : Γ(V.left, ⊤))
    (z : Γ(V.left, ⊤) ⊗[R] Γ(A.left, ⊤)) :
    tripleCoordinates β p q j hq hp l (s ⊗ₜ[R] z) =
      b.left.appTop (coordinates j z) * (a ≫ p ≫ β).left.appTop s := by
  change coordinates l (extendedCoordinates β p q j hq hp (s ⊗ₜ[R] z)) = _
  rw [extendedCoordinates_tmul]
  exact coordinates_tmul (p ≫ β) a b l hlb hla s _

include hlb hla hab in
/-- Tensoring the actual coaction evaluates along the original first arrow. -/
theorem tripleCoordinates_transport (z : Γ(V.left, ⊤) ⊗[R] Γ(A.left, ⊤)) :
    let _ := coefficientAlgebra β
    let _ := coefficientTower β
    tripleCoordinates β p q j hq hp l
      (((coaction β p q j hq hp).toLinearMap.restrictScalars R).lTensor Γ(V.left, ⊤) z) =
        a.left.appTop (coordinates j z) := by
  let _ := coefficientAlgebra β
  let _ := coefficientTower β
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s x =>
    change tripleCoordinates β p q j hq hp l (s ⊗ₜ[R] coaction β p q j hq hp x) = _
    rw [tripleCoordinates_tmul β p q j hq hp a b l hlb hla,
      coaction_apply, coordinates_source, coordinates_tmul β p q j hq hp, map_mul]
    change (b ≫ p).left.appTop x * (a ≫ p ≫ β).left.appTop s =
      (a ≫ q).left.appTop x * (a ≫ p ≫ β).left.appTop s
    rw [hab]

include hlb hla hmp hmq in
/-- Inserting the tensor unit evaluates along the actual composite arrow. -/
theorem tripleCoordinates_insert (z : Γ(V.left, ⊤) ⊗[R] Γ(A.left, ⊤)) :
    tripleCoordinates β p q j hq hp l (AffineTensorCocycle.insertMiddle 1 z) =
      m.left.appTop (coordinates j z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s x =>
    change tripleCoordinates β p q j hq hp l (s ⊗ₜ[R] (1 ⊗ₜ[R] x)) = _
    rw [tripleCoordinates_tmul β p q j hq hp a b l hlb hla,
      coordinates_test β p q j hq hp, coordinates_tmul β p q j hq hp, map_mul]
    change (b ≫ q).left.appTop x * (a ≫ p ≫ β).left.appTop s =
      (m ≫ q).left.appTop x * (m ≫ p ≫ β).left.appTop s
    rw [hmq, ← Category.assoc m, hmp, Category.assoc]

include hlb hla hab hmp hmq in
/-- The original geometric composition laws prove coassociativity of multiplicative transport. -/
theorem coaction_coassoc (x : Γ(A.left, ⊤)) :
    let _ := coefficientAlgebra β
    let _ := coefficientTower β
    ((coaction β p q j hq hp).toLinearMap.restrictScalars R).lTensor Γ(V.left, ⊤)
      (coaction β p q j hq hp x) =
        AffineTensorCocycle.insertMiddle 1 (coaction β p q j hq hp x) := by
  let _ := coefficientAlgebra β
  let _ := coefficientTower β
  apply (tripleCoordinates β p q j hq hp l).injective
  rw [tripleCoordinates_transport β p q j hq hp a b l hlb hla hab,
    tripleCoordinates_insert β p q j hq hp a b m l hlb hla hmp hmq,
    coaction_apply, coordinates_source]
  change (a ≫ p).left.appTop x = (m ≫ p).left.appTop x
  rw [hmp]

end FLT.Mazur.SchemeRelationTensor

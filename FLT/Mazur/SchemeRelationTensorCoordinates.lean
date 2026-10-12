/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineProductTensorCoordinates
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Multiplicative coordinates for a full relation envelope

An actual relation envelope isomorphism identifies its section ring with the
literal tensor ring. The two independent coefficient maps are retained.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
namespace FLT.Mazur.SchemeRelationTensor
open Approximation AffineProductTensorCoordinates
universe u
set_option backward.isDefEq.respectTransparency false
variable {R : Type u} [CommRing R] {A V Z : Over (Spec (.of R))}
  [IsAffine A.left] [IsAffine V.left]
  (β : A ⟶ V) (p q : Z ⟶ A) (j : Z ⟶ prod A V)
  (hq : j ≫ prod.fst = q) (hp : j ≫ prod.snd = p ≫ β)
/-- The algebra induced by the original structural morphism. -/
local instance sourceAlgebra : Algebra R Γ(A.left, ⊤) := affineBaseSectionAlgebra A.hom
/-- The algebra induced by the original structural morphism. -/
local instance baseAlgebra : Algebra R Γ(V.left, ⊤) := affineBaseSectionAlgebra V.hom

/-- The source's algebra structure over its original translation base. -/
abbrev coefficientAlgebra : Algebra Γ(V.left, ⊤) Γ(A.left, ⊤) := β.left.appTop.hom.toAlgebra

omit [IsAffine A.left] [IsAffine V.left] in
/-- The original base map makes the two coefficient structures a scalar tower. -/
theorem coefficientTower :
    let _ := coefficientAlgebra β
    IsScalarTower R Γ(V.left, ⊤) Γ(A.left, ⊤) := by
  let _ := coefficientAlgebra β
  apply IsScalarTower.of_algebraMap_eq
  intro r
  exact (affineBaseSectionHom A.hom V.hom β.left β.w).commutes r |>.symm

variable [IsIso j.left]

/-- The full original envelope gives a multiplicative tensor coordinate equivalence. -/
def coordinates : Γ(V.left, ⊤) ⊗[R] Γ(A.left, ⊤) ≃+* Γ(Z.left, ⊤) :=
  (Algebra.TensorProduct.comm R Γ(V.left, ⊤) Γ(A.left, ⊤)).toRingEquiv.trans
    ((tensorIso A V).commRingCatIsoToRingEquiv.trans
      (Scheme.Γ.mapIso (asIso j.left).op).commRingCatIsoToRingEquiv)

include hp hq in
/-- A pure tensor retains the second endpoint and the first endpoint's independent base map. -/
theorem coordinates_tmul (s : Γ(V.left, ⊤)) (b : Γ(A.left, ⊤)) :
    coordinates j (s ⊗ₜ[R] b) = q.left.appTop b * (p ≫ β).left.appTop s := by
  change j.left.appTop ((tensorIso A V).hom (b ⊗ₜ[R] s)) = _
  rw [tensorIso_tmul, map_mul]
  change (j ≫ prod.fst).left.appTop b * (j ≫ prod.snd).left.appTop s = _
  rw [hq, hp]

/-- Pullback of the actual first endpoint, transported into literal tensor coordinates. -/
def sourceRingMap : Γ(A.left, ⊤) →+* Γ(V.left, ⊤) ⊗[R] Γ(A.left, ⊤) :=
  (coordinates j).symm.toRingHom.comp p.left.appTop.hom

/-- The constructed map retains the original first endpoint on every coefficient. -/
theorem coordinates_source (b : Γ(A.left, ⊤)) :
    coordinates j (sourceRingMap p j b) = p.left.appTop b :=
  (coordinates j).apply_symm_apply _

include hp hq in
/-- The other original endpoint is precisely the tensor unit inclusion. -/
theorem coordinates_test (b : Γ(A.left, ⊤)) :
    coordinates j (1 ⊗ₜ[R] b) = q.left.appTop b := by
  rw [coordinates_tmul β p q j hq hp, map_one, mul_one]

include hp hq in
/-- The first endpoint's original base scalar becomes the independent first tensor factor. -/
theorem sourceRingMap_scalar (s : Γ(V.left, ⊤)) :
    sourceRingMap p j (β.left.appTop s) = s ⊗ₜ[R] (1 : Γ(A.left, ⊤)) := by
  apply (coordinates j).injective
  rw [coordinates_source, coordinates_tmul β p q j hq hp, map_one, one_mul]
  rfl

/-- The actual multiplicative endpoint transport respects the original base coefficients. -/
def coaction :
    let _ := coefficientAlgebra β
    Γ(A.left, ⊤) →ₐ[Γ(V.left, ⊤)] Γ(V.left, ⊤) ⊗[R] Γ(A.left, ⊤) := by
  let _ := coefficientAlgebra β
  exact ⟨sourceRingMap p j, sourceRingMap_scalar β p q j hq hp⟩

/-- The algebra coaction is the original endpoint pullback in the same tensor coordinates. -/
theorem coaction_apply (b : Γ(A.left, ⊤)) :
    coaction β p q j hq hp b = sourceRingMap p j b := rfl

end FLT.Mazur.SchemeRelationTensor

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianOverlapAffineCoordinates

/-!
# Original ring maps as coefficient refinements

Present the recovered coefficient refinement with its original ring homomorphism
as a definitional field. This avoids transporting sheaf pullbacks across equality.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GrassmannianOverlapAffineCoordinates
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] {X : Scheme.{u}}
variable (p : X ⟶ Spec (.of A)) (q : X ⟶ Spec (.of B))
  (w : p ≫ Spec.algebraMap R A = q ≫ Spec.algebraMap R B)
variable {D E : CommRingCat.{u}} (z : Spec D ⟶ X)

variable (z' : Spec E ⟶ X) (α : D ⟶ E) (h : Spec.map α ≫ z = z')

/-- The same coefficient refinement, retaining the original ring map definitionally. -/
def directRefine :
    let _ := coefficientAlgebra (R := R) p z
    let _ := coefficientAlgebra (R := R) p z'
    D →ₐ[R] E := by
  let _ := coefficientAlgebra (R := R) p z
  let _ := coefficientAlgebra (R := R) p z'
  refine { α.hom with commutes' := ?_ }
  intro r
  rw [← refine_ringHom (R := R) p z z' α h]
  exact (refine (R := R) p z z' α h).commutes r

/-- The direct presentation equals the independently recovered refinement. -/
theorem directRefine_eq :
    let _ := coefficientAlgebra (R := R) p z
    let _ := coefficientAlgebra (R := R) p z'
    directRefine (R := R) p z z' α h = refine (R := R) p z z' α h := by
  let _ := coefficientAlgebra (R := R) p z
  let _ := coefficientAlgebra (R := R) p z'
  apply AlgHom.coe_ringHom_injective
  exact (refine_ringHom (R := R) p z z' α h).symm

/-- The underlying ring homomorphism is exactly the input map. -/
theorem directRefine_ringHom :
    let _ := coefficientAlgebra (R := R) p z
    let _ := coefficientAlgebra (R := R) p z'
    (directRefine (R := R) p z z' α h).toRingHom = α.hom := rfl

/-- First coordinates commute with the original ring-map presentation. -/
theorem directRefine_left :
    let _ := coefficientAlgebra (R := R) p z
    let _ := coefficientAlgebra (R := R) p z'
    (directRefine (R := R) p z z' α h).comp (left (R := R) p z) = left (R := R) p z' := by
  let _ := coefficientAlgebra (R := R) p z
  let _ := coefficientAlgebra (R := R) p z'
  rw [directRefine_eq]
  exact refine_left p z z' α h

/-- Second coordinates commute with the same original ring-map presentation. -/
theorem directRefine_right :
    let _ := coefficientAlgebra (R := R) p z
    let _ := coefficientAlgebra (R := R) p z'
    (directRefine (R := R) p z z' α h).comp (right p q w z) = right p q w z' := by
  let _ := coefficientAlgebra (R := R) p z
  let _ := coefficientAlgebra (R := R) p z'
  rw [directRefine_eq]
  exact refine_right p q w z z' α h

end FLT.Mazur.GrassmannianOverlapAffineCoordinates

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineMorphismAlgebraMap

/-!
# Coefficient coordinates on arbitrary Grassmannian overlaps

Every affine test of an overlap has its actual coefficient algebra. The two
coordinate maps and every further affine refinement are algebra homomorphisms.
No affineness assumption is made on the overlap itself.
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

/-- The actual coefficient algebra on an affine test of the overlap. -/
abbrev coefficientAlgebra : Algebra R D :=
  (Spec.preimage (z ≫ p ≫ Spec.algebraMap R A)).hom.toAlgebra

/-- The coefficient spectrum map is the original geometric composite. -/
theorem coefficientAlgebra_spec :
    let _ := coefficientAlgebra (R := R) p z
    Spec.algebraMap R D = z ≫ p ≫ Spec.algebraMap R A :=
  Spec.map_preimage _

/-- The first original affine chart coordinate. -/
def left :
    let _ := coefficientAlgebra (R := R) p z
    A →ₐ[R] D := by
  let _ := coefficientAlgebra (R := R) p z
  exact affineOverAlgHom R A D (z ≫ p) (by
    change (z ≫ p) ≫ Spec.algebraMap R A = Spec.algebraMap R D
    rw [coefficientAlgebra_spec, Category.assoc])

/-- The second chart coordinate uses the same coefficient algebra. -/
def right :
    let _ := coefficientAlgebra (R := R) p z
    B →ₐ[R] D := by
  let _ := coefficientAlgebra (R := R) p z
  exact affineOverAlgHom R B D (z ≫ q) (by
    change (z ≫ q) ≫ Spec.algebraMap R B = Spec.algebraMap R D
    rw [coefficientAlgebra_spec, Category.assoc, w])

/-- Taking the spectrum recovers the first original chart path. -/
theorem left_spec :
    let _ := coefficientAlgebra (R := R) p z
    Spec.map (CommRingCat.ofHom (left (R := R) p z).toRingHom) = z ≫ p := by
  let _ := coefficientAlgebra (R := R) p z
  exact Spec.map_preimage _

/-- Taking the spectrum recovers the second original chart path. -/
theorem right_spec :
    let _ := coefficientAlgebra (R := R) p z
    Spec.map (CommRingCat.ofHom (right p q w z).toRingHom) = z ≫ q := by
  let _ := coefficientAlgebra (R := R) p z
  exact Spec.map_preimage _

variable (z' : Spec E ⟶ X) (α : D ⟶ E) (h : Spec.map α ≫ z = z')

/-- A geometric affine refinement induces its original coefficient algebra map. -/
def refine :
    let _ := coefficientAlgebra (R := R) p z
    let _ := coefficientAlgebra (R := R) p z'
    D →ₐ[R] E := by
  let _ := coefficientAlgebra (R := R) p z
  let _ := coefficientAlgebra (R := R) p z'
  exact affineOverAlgHom R D E (Spec.map α) (by
    change Spec.map α ≫ Spec.algebraMap R D = Spec.algebraMap R E
    rw [coefficientAlgebra_spec, coefficientAlgebra_spec,
      ← Category.assoc (Spec.map α) z, h])

/-- Refinement retains the exact input ring map. -/
theorem refine_ringHom :
    let _ := coefficientAlgebra (R := R) p z
    let _ := coefficientAlgebra (R := R) p z'
    (refine (R := R) p z z' α h).toRingHom = α.hom := by
  apply CommRingCat.hom_ext_iff.mp
  exact Spec.preimage_map α

/-- The spectrum of the refinement map is the given affine test refinement. -/
theorem refine_spec :
    let _ := coefficientAlgebra (R := R) p z
    let _ := coefficientAlgebra (R := R) p z'
    Spec.map (CommRingCat.ofHom (refine (R := R) p z z' α h).toRingHom) =
      Spec.map α := by
  let _ := coefficientAlgebra (R := R) p z
  let _ := coefficientAlgebra (R := R) p z'
  exact Spec.map_preimage _

/-- First chart coordinates commute with every actual affine refinement. -/
theorem refine_left :
    let _ := coefficientAlgebra (R := R) p z
    let _ := coefficientAlgebra (R := R) p z'
    (refine (R := R) p z z' α h).comp (left (R := R) p z) = left (R := R) p z' := by
  let _ := coefficientAlgebra (R := R) p z
  let _ := coefficientAlgebra (R := R) p z'
  apply AlgHom.coe_ringHom_injective
  apply (CommRingCat.hom_ext_iff
    (f := CommRingCat.ofHom _) (g := CommRingCat.ofHom _)).mp
  apply Spec.map_injective
  change Spec.map (CommRingCat.ofHom (left (R := R) p z).toRingHom ≫
    CommRingCat.ofHom (refine (R := R) p z z' α h).toRingHom) =
      Spec.map (CommRingCat.ofHom (left (R := R) p z').toRingHom)
  rw [Spec.map_comp, left_spec, left_spec, refine_spec, ← Category.assoc, h]

/-- Second chart coordinates commute with the same actual affine refinement. -/
theorem refine_right :
    let _ := coefficientAlgebra (R := R) p z
    let _ := coefficientAlgebra (R := R) p z'
    (refine (R := R) p z z' α h).comp (right p q w z) = right p q w z' := by
  let _ := coefficientAlgebra (R := R) p z
  let _ := coefficientAlgebra (R := R) p z'
  apply AlgHom.coe_ringHom_injective
  apply (CommRingCat.hom_ext_iff
    (f := CommRingCat.ofHom _) (g := CommRingCat.ofHom _)).mp
  apply Spec.map_injective
  change Spec.map (CommRingCat.ofHom (right p q w z).toRingHom ≫
    CommRingCat.ofHom (refine (R := R) p z z' α h).toRingHom) =
      Spec.map (CommRingCat.ofHom (right p q w z').toRingHom)
  rw [Spec.map_comp, right_spec, right_spec, refine_spec, ← Category.assoc, h]

end FLT.Mazur.GrassmannianOverlapAffineCoordinates

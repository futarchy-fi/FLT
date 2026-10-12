/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianMorphismLocalQuotient

/-!
# Actual tensor intersections of recovered local quotient data

The coefficient tensor product is the scheme intersection of two principal
refinements. The recovered original quotients agree there as complete Grassmannian
points, with all relations and finite projective quotient data retained.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A M κ : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Fintype κ] {d : ℕ}
variable (f : Spec (.of A) ⟶ ambientGrassmannianScheme R M κ d)
  (hf : f ≫ ambientGrassmannianStructure R M κ d = Spec.algebraMap R A)

/-- The two coefficient-local quotient relations agree on their actual tensor intersection. -/
theorem ambientMorphismLocalPoint_tensor_compatible (p q : AmbientMorphismCoverIndex f) :
    Module.Grassmannian.map
      ((Algebra.TensorProduct.includeLeft : Localization.Away p.2.val →ₐ[A]
        Localization.Away p.2.val ⊗[A] Localization.Away q.2.val).restrictScalars R)
      (ambientMorphismLocalPoint f hf p).val =
    Module.Grassmannian.map
      ((Algebra.TensorProduct.includeRight : Localization.Away q.2.val →ₐ[A]
        Localization.Away p.2.val ⊗[A] Localization.Away q.2.val).restrictScalars R)
      (ambientMorphismLocalPoint f hf q).val := by
  apply ambientMorphismLocalPoint_compatible
  apply AlgHom.ext
  intro a
  exact (Algebra.TensorProduct.includeLeft.commutes a).trans
    (Algebra.TensorProduct.includeRight.commutes a).symm

omit [Algebra R A] in
/-- The tensor intersection is the categorical pullback of the actual coefficient open maps. -/
theorem ambientMorphismCover_tensor_isPullback (p q : AmbientMorphismCoverIndex f) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeft : Localization.Away p.2.val →ₐ[A]
          Localization.Away p.2.val ⊗[A] Localization.Away q.2.val).toRingHom))
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : Localization.Away q.2.val →ₐ[A]
          Localization.Away p.2.val ⊗[A] Localization.Away q.2.val).toRingHom))
      (Spec.algebraMap A (Localization.Away p.2.val))
      (Spec.algebraMap A (Localization.Away q.2.val)) :=
  isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct A (Localization.Away p.2.val)
      (Localization.Away q.2.val))

end FLT.Mazur.GrassmannianChart

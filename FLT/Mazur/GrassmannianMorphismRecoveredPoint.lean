/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianMorphismFiniteProjective

/-!
# Recovering an original Grassmannian point from every affine scheme test

The intersected relation now has a finite projective quotient of the required
rank, so it defines an actual original Grassmannian point. Both inverse laws
hold for the global classifying morphism, retaining the fixed complement size.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A M κ : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Fintype κ] {d : ℕ}
variable (f : Spec (.of A) ⟶ ambientGrassmannianScheme R M κ d)
  (hf : f ≫ ambientGrassmannianStructure R M κ d = Spec.algebraMap R A)

/-- The original quotient recovered from an arbitrary base-preserving affine scheme test. -/
def ambientMorphismPoint : Module.Grassmannian A (A ⊗[R] M) d where
  toSubmodule := ambientMorphismRelation f hf
  finite_quotient := inferInstance
  projective_quotient := inferInstance
  rankAtStalk_eq := ambientMorphismQuotient_rank f hf

/-- Every local functor image is exactly the original recovered chart quotient. -/
theorem ambientMorphismPoint_local (q : AmbientMorphismCoverIndex f) :
    Module.Grassmannian.map (IsScalarTower.toAlgHom R A (Localization.Away q.2.val))
      (ambientMorphismPoint f hf) = (ambientMorphismLocalPoint f hf q).val := by
  apply Module.Grassmannian.ext
  apply Submodule.restrictScalars_injective A
  rw [grassmannian_localized_relation]
  exact congrArg (Submodule.restrictScalars A) (ambientMorphismRelation_localized_eq f hf q)

variable {ι : Type u} [Fintype ι] (b : Module.Basis ι R M)
  (hκ : Fintype.card κ = Fintype.card ι - d)

/-- The recovered quotient classifies the given entire scheme morphism. -/
theorem ambientMorphismPoint_classifies :
    ambientClassifyingMap b (ambientMorphismPoint f hf) hκ = f :=
  ambientClassifyingMap_eq_of_localRecovery f hf b _ hκ (ambientMorphismPoint_local f hf)

/-- Recovering a classified original quotient gives back that whole original point. -/
theorem ambientMorphismPoint_ofClassifying (N : Module.Grassmannian A (A ⊗[R] M) d) :
    ambientMorphismPoint (ambientClassifyingMap b N hκ)
      (ambientClassifyingMap_over b N hκ) = N := by
  apply Module.Grassmannian.ext
  exact ambientMorphismRelation_ofClassifying b N hκ

/-- Global affine classification is a genuine equivalence for every coefficient algebra. -/
def ambientGrassmannianPointEquiv :
    Module.Grassmannian A (A ⊗[R] M) d ≃
      {f : Spec (.of A) ⟶ ambientGrassmannianScheme R M κ d //
        f ≫ ambientGrassmannianStructure R M κ d = Spec.algebraMap R A} where
  toFun N := ⟨ambientClassifyingMap b N hκ, ambientClassifyingMap_over b N hκ⟩
  invFun f := ambientMorphismPoint f.val f.property
  left_inv := ambientMorphismPoint_ofClassifying b hκ
  right_inv f := Subtype.ext (ambientMorphismPoint_classifies f.val f.property b hκ)

end FLT.Mazur.GrassmannianChart

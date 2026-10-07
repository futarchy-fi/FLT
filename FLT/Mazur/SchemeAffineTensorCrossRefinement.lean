/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossRefinement

/-!
# Constructing a cross refinement by a tensor product of affine covers

Two faithfully flat affine covers of the same affine base have a common
faithfully flat tensor-product cover. Its two maps into the original covering
scheme are kept separate, so it supplies an actual cross refinement.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
universe u
namespace FLT.Mazur.SchemeAffineTensorCrossRefinement
open SchemeAffineDescent
variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]

/-- The tensor product of two faithfully flat algebras is faithfully flat over the base. -/
theorem tensor_faithfullyFlat [Module.FaithfullyFlat R S] [Module.FaithfullyFlat R T] :
    (algebraMap R (S ⊗[R] T)).FaithfullyFlat := by
  rw [RingHom.faithfullyFlat_algebraMap_iff]
  exact Module.FaithfullyFlat.trans R S (S ⊗[R] T)

variable {X Y : Scheme.{u}} (p : Y ⟶ X) (a : Spec (.of R) ⟶ X)
variable (b : Spec (.of S) ⟶ Y) (c : Spec (.of T) ⟶ Y)
variable (wb : Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ a = b ≫ p)
variable (wc : Spec.map (CommRingCat.ofHom (algebraMap R T)) ≫ a = c ≫ p)

/-- A supplied faithfully flat algebra chart, expressed as the geometric chart structure. -/
def algebraChart [Module.FaithfullyFlat R S] : Chart p where
  baseRing := .of R
  coverRing := .of S
  ringMap := CommRingCat.ofHom (algebraMap R S)
  faithfullyFlat := RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  base := a
  cover := b
  square := wb

/-- The actual tensor-product cover gives a cross refinement of the two algebra charts. -/
def tensorCrossRefinement [Module.FaithfullyFlat R S] [Module.FaithfullyFlat R T] :
    (algebraChart R S p a b wb).CrossRefinement (algebraChart R T p a c wc) where
  baseRing := .of R
  coverRing := .of (S ⊗[R] T)
  ringMap := CommRingCat.ofHom (algebraMap R (S ⊗[R] T))
  faithfullyFlat := tensor_faithfullyFlat R S T
  leftBase := 𝟙 _
  rightBase := 𝟙 _
  leftCover := CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T)
  rightCover := CommRingCat.ofHom (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T)
  leftSquare := by
    ext x
    exact (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] T).commutes x
  rightSquare := by
    ext x
    exact (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).commutes x
  base_over := rfl

end FLT.Mazur.SchemeAffineTensorCrossRefinement

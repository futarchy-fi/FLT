/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianQuotientAtlasClassifying
public import FLT.Mazur.GrassmannianMorphismSheafTransition

/-!
# Arbitrary-source Grassmannian morphisms and original quotient atlases

Every scheme morphism produces a compatible atlas retaining all original
relations. Classification and recovery are mutually inverse on that atlas.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TensorProduct
open CategoryTheory.Limits
namespace FLT.Mazur.GrassmannianChart
open GrassmannianOverlapAffineCoordinates
universe u
variable {R M ι κ : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] [Fintype κ] {d : ℕ}
variable (b : Module.Basis ι R M) (hκ : Fintype.card κ = Fintype.card ι - d)
variable {X : Scheme.{u}} (C : X.AffineOpenCover) [∀ j, Algebra R (C.X j)]
variable (β : X ⟶ Spec (.of R)) (hC : ∀ j, C.f j ≫ β = Spec.algebraMap R (C.X j))
variable (f : X ⟶ ambientGrassmannianScheme R M κ d)
  (hf : f ≫ ambientGrassmannianStructure R M κ d = β)

/-- The recovered original points on the specified affine cover of any source scheme. -/
def quotientAtlasMorphismPoints (j : C.I₀) :
    Module.Grassmannian (C.X j) ((C.X j) ⊗[R] M) d :=
  ambientMorphismPoint (C.f j ≫ f) (by rw [Category.assoc, hf, hC j])

include b hκ in
/-- Recovery retains equality of every original relation on all common affine tests. -/
theorem quotientAtlasMorphismPoints_compatible :
    QuotientAtlasCompatible C β hC (quotientAtlasMorphismPoints C β hC f hf) := by
  intro j k D z
  let _ := coefficientAlgebra (R := R) (pullback.fst (C.f j) (C.f k)) z
  unfold quotientAtlasMorphismPoints
  apply ambientMorphismPoint_commonRefinement b hκ
    ⟨C.f j ≫ f, by rw [Category.assoc, hf, hC j]⟩
    ⟨C.f k ≫ f, by rw [Category.assoc, hf, hC k]⟩
  rw [left_spec, right_spec]
  simp only [Category.assoc, pullback.condition_assoc]

/-- Classifying the recovered original atlas gives the entire original scheme morphism. -/
theorem quotientAtlasMorphismPoints_classifies :
    quotientAtlasClassifyingMap b hκ C β hC (quotientAtlasMorphismPoints C β hC f hf)
      (quotientAtlasMorphismPoints_compatible b hκ C β hC f hf) = f := by
  symm
  apply quotientAtlasClassifyingMap_unique
  intro j
  exact (ambientMorphismPoint_classifies (C.f j ≫ f) _ b hκ).symm

/-- Original compatible quotient atlases represent all morphisms from the specified scheme. -/
def quotientAtlasEquiv :
    {N : ∀ j, Module.Grassmannian (C.X j) ((C.X j) ⊗[R] M) d //
      QuotientAtlasCompatible C β hC N} ≃
    {f : X ⟶ ambientGrassmannianScheme R M κ d //
      f ≫ ambientGrassmannianStructure R M κ d = β} where
  toFun N := ⟨quotientAtlasClassifyingMap b hκ C β hC N.val N.property,
    quotientAtlasClassifyingMap_over b hκ C β hC N.val N.property⟩
  invFun f := ⟨quotientAtlasMorphismPoints C β hC f.val f.property,
    quotientAtlasMorphismPoints_compatible b hκ C β hC f.val f.property⟩
  left_inv N := by
    apply Subtype.ext
    funext j
    exact quotientAtlasClassifyingMap_point b hκ C β hC N.val N.property j _
  right_inv f := Subtype.ext (quotientAtlasMorphismPoints_classifies b hκ C β hC
    f.val f.property)

end FLT.Mazur.GrassmannianChart

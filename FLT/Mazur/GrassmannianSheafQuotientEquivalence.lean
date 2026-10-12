/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianSheafQuotientClassifying
public import FLT.Mazur.GrassmannianCanonicalImageRepresentative

/-!
# Natural equivalence for actual locally free quotient isomorphism classes

The inverse constructs the entire descended quotient on the fixed canonical
source cover. Both inverse laws retain the original base and full ambient map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R M ι κ : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] [Fintype κ] {d : ℕ}
variable {X : Scheme.{u}} (β : X ⟶ Spec (.of R))
variable (b : Module.Basis ι R M) (hκ : Fintype.card κ = Fintype.card ι - d)

/-- The actual canonical-cover quotient class of a morphism over the original base. -/
def sheafQuotientImageClass
    (f : {f : X ⟶ ambientGrassmannianScheme R M κ d //
      f ≫ ambientGrassmannianStructure R M κ d = β}) :
    LocallyFreeSheafQuotientClass (M := M) β d :=
  Quotient.mk _ (imageRepresentativeOver b hκ f.val β f.property)

/-- Classifying the actual fixed-cover image returns the entire original scheme morphism. -/
theorem sheafQuotientClassifying_imageClass
    (f : {f : X ⟶ ambientGrassmannianScheme R M κ d //
      f ≫ ambientGrassmannianStructure R M κ d = β}) :
    sheafQuotientClassifying β b hκ (sheafQuotientImageClass β b hκ f) = f := by
  apply Subtype.ext
  exact ((imageRepresentativeOver b hκ f.val β f.property).classifyingMorphism_spec β b hκ).unique
    β _ b hκ (imageRepresentativeOver_classifies b hκ f.val β f.property)

/-- Recover every original quotient class from its actual fixed-cover image. -/
theorem sheafQuotientImageClass_classifying (P : LocallyFreeSheafQuotientClass (M := M) β d) :
    sheafQuotientImageClass β b hκ (sheafQuotientClassifying β b hκ P) = P := by
  apply sheafQuotientClassifying_injective β b hκ
  exact sheafQuotientClassifying_imageClass β b hκ _

/-- Actual rank-d locally free quotient classes are represented by the Grassmannian scheme. -/
def sheafQuotientEquiv : LocallyFreeSheafQuotientClass (M := M) β d ≃
    {f : X ⟶ ambientGrassmannianScheme R M κ d //
      f ≫ ambientGrassmannianStructure R M κ d = β} where
  toFun := sheafQuotientClassifying β b hκ
  invFun := sheafQuotientImageClass β b hκ
  left_inv := sheafQuotientImageClass_classifying β b hκ
  right_inv := sheafQuotientClassifying_imageClass β b hκ

/-- The representing equivalence commutes with arbitrary source-scheme pullback. -/
theorem sheafQuotientEquiv_natural {Y : Scheme.{u}} (g : Y ⟶ X)
    (P : LocallyFreeSheafQuotientClass (M := M) β d) :
    (sheafQuotientEquiv (g ≫ β) b hκ
      (locallyFreeSheafQuotientClassPullback β d g P)).val =
      g ≫ (sheafQuotientEquiv β b hκ P).val :=
  sheafQuotientClassifying_pullback β b hκ g P

/-- Pulling back the actual canonical-cover image agrees with imaging the composite morphism. -/
theorem sheafQuotientImageClass_natural {Y : Scheme.{u}} (g : Y ⟶ X)
    (f : {f : X ⟶ ambientGrassmannianScheme R M κ d //
      f ≫ ambientGrassmannianStructure R M κ d = β}) :
    locallyFreeSheafQuotientClassPullback β d g (sheafQuotientImageClass β b hκ f) =
      sheafQuotientImageClass (g ≫ β) b hκ
        ⟨g ≫ f.val, by rw [Category.assoc, f.property]⟩ := by
  apply sheafQuotientClassifying_injective (g ≫ β) b hκ
  apply Subtype.ext
  rw [sheafQuotientClassifying_pullback, sheafQuotientClassifying_imageClass,
    sheafQuotientClassifying_imageClass]

end FLT.Mazur.GrassmannianChart

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianMorphismRecoveredPoint
public import FLT.Mazur.GrassmannianOverlapAffineCoordinates

/-!
# Classifying an original quotient atlas on an arbitrary scheme

Full original relations compatible on affine tests of the actual intersections
construct a global scheme morphism. Both its local quotient recovery and its
uniqueness hold without assuming the source or its intersections affine.
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

include hC in
/-- The original chart algebras have the same base on their entire actual intersection. -/
theorem quotientAtlas_overlapBase (j k : C.I₀) :
    pullback.fst (C.f j) (C.f k) ≫ Spec.algebraMap R (C.X j) =
      pullback.snd (C.f j) (C.f k) ≫ Spec.algebraMap R (C.X k) := by
  rw [← hC j, ← hC k, ← Category.assoc, pullback.condition, Category.assoc]

variable (N : ∀ j, Module.Grassmannian (C.X j) ((C.X j) ⊗[R] M) d)

/-- Compatibility retains equality of the full relations on every affine overlap test. -/
def QuotientAtlasCompatible : Prop :=
  ∀ (j k : C.I₀) {D : CommRingCat.{u}} (z : Spec D ⟶ pullback (C.f j) (C.f k)),
    let _ := coefficientAlgebra (R := R) (pullback.fst (C.f j) (C.f k)) z
    Module.Grassmannian.map (left (R := R) (pullback.fst (C.f j) (C.f k)) z) (N j) =
      Module.Grassmannian.map (right (pullback.fst (C.f j) (C.f k))
        (pullback.snd (C.f j) (C.f k)) (quotientAtlas_overlapBase C β hC j k) z) (N k)

variable (hN : QuotientAtlasCompatible C β hC N)

include hN in
/-- Full relation compatibility yields actual scheme compatibility on entire intersections. -/
theorem quotientAtlasClassifying_compatible (j k : C.I₀) :
    pullback.fst (C.f j) (C.f k) ≫ ambientClassifyingMap b (N j) hκ =
      pullback.snd (C.f j) (C.f k) ≫ ambientClassifyingMap b (N k) hκ := by
  apply (pullback (C.f j) (C.f k)).affineOpenCover.openCover.hom_ext
  intro t
  let z := (pullback (C.f j) (C.f k)).affineOpenCover.f t
  let _ := coefficientAlgebra (R := R) (pullback.fst (C.f j) (C.f k)) z
  have hl := ambientClassifyingMap_natural b (N j) hκ
    (left (R := R) (pullback.fst (C.f j) (C.f k)) z)
  have hr := ambientClassifyingMap_natural b (N k) hκ
    (right (pullback.fst (C.f j) (C.f k)) (pullback.snd (C.f j) (C.f k))
      (quotientAtlas_overlapBase C β hC j k) z)
  rw [left_spec, Category.assoc] at hl
  rw [right_spec, Category.assoc] at hr
  exact hl.symm.trans ((congrArg (fun P ↦ ambientClassifyingMap b P hκ)
    (hN j k z)).trans hr)

/-- Construct the global classifying scheme morphism from an original quotient atlas. -/
@[irreducible] def quotientAtlasClassifyingMap : X ⟶ ambientGrassmannianScheme R M κ d :=
  C.openCover.glueMorphisms (fun j ↦ ambientClassifyingMap b (N j) hκ)
    (quotientAtlasClassifying_compatible b hκ C β hC N hN)

/-- The global classifying map recovers every original affine chart classification. -/
@[reassoc] theorem quotientAtlasClassifyingMap_chart (j : C.I₀) :
    C.f j ≫ quotientAtlasClassifyingMap b hκ C β hC N hN =
      ambientClassifyingMap b (N j) hκ := by
  unfold quotientAtlasClassifyingMap
  exact C.openCover.ι_glueMorphisms _ _ j

/-- The constructed classification retains the original base morphism. -/
@[reassoc] theorem quotientAtlasClassifyingMap_over :
    quotientAtlasClassifyingMap b hκ C β hC N hN ≫ ambientGrassmannianStructure R M κ d =
      β := by
  apply C.openCover.hom_ext
  intro j
  change C.f j ≫ quotientAtlasClassifyingMap b hκ C β hC N hN ≫
    ambientGrassmannianStructure R M κ d = C.f j ≫ β
  rw [quotientAtlasClassifyingMap_chart_assoc, ambientClassifyingMap_over, hC j]

/-- The classifying morphism is uniquely determined by its original quotient atlas. -/
theorem quotientAtlasClassifyingMap_unique
    (f : X ⟶ ambientGrassmannianScheme R M κ d)
    (hf : ∀ j, C.f j ≫ f = ambientClassifyingMap b (N j) hκ) :
    f = quotientAtlasClassifyingMap b hκ C β hC N hN := by
  apply C.openCover.hom_ext
  intro j
  exact (hf j).trans (quotientAtlasClassifyingMap_chart b hκ C β hC N hN j).symm

/-- Recovering the constructed classification returns the entire original chart point. -/
theorem quotientAtlasClassifyingMap_point (j : C.I₀)
    (hj : (C.f j ≫ quotientAtlasClassifyingMap b hκ C β hC N hN) ≫
      ambientGrassmannianStructure R M κ d = Spec.algebraMap R (C.X j)) :
    ambientMorphismPoint (C.f j ≫ quotientAtlasClassifyingMap b hκ C β hC N hN) hj =
      N j := by
  apply ambientClassifyingMap_injective b hκ
  dsimp only
  rw [ambientMorphismPoint_classifies, quotientAtlasClassifyingMap_chart]

end FLT.Mazur.GrassmannianChart

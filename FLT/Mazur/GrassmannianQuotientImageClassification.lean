/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianCanonicalSheafClassification
public import FLT.Mazur.GrassmannianQuotientImageFixedFrames
public import FLT.Mazur.GrassmannianQuotientImageAmbientEpi
public import FLT.Mazur.GrassmannianQuotientImageTest

/-!
# Classifying an actual quotient image recovers its original scheme morphism

For every original affine source cover, the actual descended quotient retains
all local projections and recovers the original scheme morphism.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.GrassmannianOpenChartDescent
open GrassmannianChart
universe u
variable {R M ι κ : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] [Fintype κ] {d : ℕ}
variable (b : Module.Basis ι R M) (hκ : Fintype.card κ = Fintype.card ι - d)
variable {X : Scheme.{u}} (f : X ⟶ ambientGrassmannianScheme R M κ d)
variable (C : X.AffineOpenCover.{u}) [aC : ∀ j, Algebra R (C.X j)]
  (a : ∀ j, {a : Spec (C.X j) ⟶ ambientGrassmannianScheme R M κ d //
    a ≫ ambientGrassmannianStructure R M κ d = Spec.algebraMap R (C.X j)})
  (h : ∀ j, C.f j ≫ f = (a j).val)
attribute [local irreducible] Scheme.Modules.pullback grassmannianQuotientSheaf

/-- The original scheme morphism classifies its actual quotient image on any affine cover. -/
theorem quotientImage_classifies :
    SheafQuotientClassifies (f ≫ ambientGrassmannianStructure R M κ d)
      (quotientImageAmbientMap b hκ f (fun j ↦ C.X j) C.f a h) b hκ f := by
  unfold SheafQuotientClassifies
  refine ⟨C, aC, (originalChart_base f (fun j ↦ C.X j) C.f a h),
    (fun j ↦ ambientMorphismPoint (a j).val (a j).property), ?_, ?_⟩
  · intro j
    exact (h j).trans (ambientMorphismPoint_classifies (a j).val (a j).property b hκ).symm
  · intro j
    exact ⟨(quotientImageSheafChartIso b hκ f (fun j ↦ C.X j) C.f a h j).symm,
      quotientImageSheafChartIso_inv_projection b hκ f (fun j ↦ C.X j) C.f a h j⟩

/-- The classifying construction recovers a morphism from its full descended image. -/
theorem locallyFreeQuotientClassifyingMap_quotientImage :
    let _ := quotientImageAmbientMap_epi b hκ f (fun j ↦ C.X j) C.f a h
      C.openCover.iSup_opensRange
    locallyFreeQuotientClassifyingMap (f ≫ ambientGrassmannianStructure R M κ d)
      (quotientImageAmbientMap b hκ f (fun j ↦ C.X j) C.f a h) b hκ
      (quotientImageSheaf_fixedFrames b hκ f (fun j ↦ C.X j) C.f a h
        C.openCover.iSup_opensRange) (by simp) = f := by
  let _ := quotientImageAmbientMap_epi b hκ f (fun j ↦ C.X j) C.f a h
    C.openCover.iSup_opensRange
  exact (locallyFreeQuotientClassifyingMap_spec _ _ b hκ
    (quotientImageSheaf_fixedFrames b hκ f (fun j ↦ C.X j) C.f a h
      C.openCover.iSup_opensRange) (by simp)).unique _ _ b hκ
        (quotientImage_classifies b hκ f C a h)

end FLT.Mazur.GrassmannianOpenChartDescent

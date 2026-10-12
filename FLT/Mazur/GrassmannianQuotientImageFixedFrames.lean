/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianSchemeImageQuotient
public import FLT.Mazur.ModuleTildeLocalFrames
public import FLT.Mazur.GrassmannianQuotientLocalBasis

/-!
# Fixed-rank local frames of the actual descended quotient

An arbitrary morphism to the Grassmannian gives compatible quotient sheaves on
its affine open charts. The whole-overlap comparisons satisfy the geometric
refinement and cocycle hypotheses of module-sheaf gluing.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.GrassmannianChart
open ModuleSheafLocalFrames
universe u
variable {R A M : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] {d : ℕ}

/-- The entire original quotient has frames with exactly d basis vectors. -/
theorem grassmannianQuotientSheaf_fixedFrames
    (N : Module.Grassmannian A (A ⊗[R] M) d) :
    HasFrames (ULift.{u} (Fin d)) (grassmannianQuotientSheaf N) := by
  unfold grassmannianQuotientSheaf
  apply ModuleTildeLocalFrames.hasFrames_of_principalBases
  intro x
  obtain ⟨r, hr, ⟨b⟩⟩ := grassmannianQuotient_localBasis N x
  exact ⟨r, hr, ⟨b.reindex Equiv.ulift.symm⟩⟩

end FLT.Mazur.GrassmannianChart

namespace FLT.Mazur.GrassmannianOpenChartDescent
open GrassmannianChart GrassmannianOverlapAffineTransition ModuleSheafLocalFrames
open ModuleSheafOpenImageChart SheafPullbackPathComparison
universe u
variable {R M ι κ : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] [Fintype κ] {d : ℕ}
variable (b : Module.Basis ι R M) (hκ : Fintype.card κ = Fintype.card ι - d)
variable {X : Scheme.{u}} (f : X ⟶ ambientGrassmannianScheme R M κ d)
variable {J : Type u} (A : J → Type u) [∀ j, CommRing (A j)] [∀ j, Algebra R (A j)]
  (i : ∀ j, Spec (.of (A j)) ⟶ X) [∀ j, IsOpenImmersion (i j)]
variable (a : ∀ j, {a : Spec (.of (A j)) ⟶ ambientGrassmannianScheme R M κ d //
  a ≫ ambientGrassmannianStructure R M κ d = Spec.algebraMap R (A j)})
  (h : ∀ j, i j ≫ f = (a j).val)
attribute [local irreducible] Scheme.Modules.pullback grassmannianQuotientSheaf overlapIso

open ModuleSheafOpenOverlapTransition ModuleSheafMorphismGluing
attribute [local irreducible] Scheme.Modules.pushforward

attribute [local irreducible] comparison

/-- Covering by the original quotient charts gives actual finite free neighborhoods globally. -/
theorem quotientImageSheaf_fixedFrames (hc : ⨆ j, (i j).opensRange = ⊤) :
    ModuleSheafLocalFrames.HasFrames (ULift.{u} (Fin d)) (quotientImageSheaf b hκ f A i a h) := by
  apply HasFrames.of_openCover (ULift.{u} (Fin d)) _ (fun j ↦ (i j).opensRange) hc
  intro j
  have hj := (grassmannianQuotientSheaf_fixedFrames
    (ambientMorphismPoint (a j).val (a j).property)).of_iso (ULift.{u} (Fin d))
      (quotientImageSheafChartIso b hκ f A i a h j).symm
  exact (hj.pullback (ULift.{u} (Fin d)) _ (i j).isoOpensRange.inv).of_iso
    (ULift.{u} (Fin d))
    ((comparison (i j).isoOpensRange.inv (i j) (i j).opensRange.ι
      (i j).isoOpensRange_inv_comp).app _)

end FLT.Mazur.GrassmannianOpenChartDescent

namespace FLT.Mazur.GrassmannianChart
universe u
variable {R M ι κ : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] [Fintype κ] {d : ℕ}
variable {X : Scheme.{u}} (f : X ⟶ ambientGrassmannianScheme R M κ d)
variable (b : Module.Basis ι R M) (hκ : Fintype.card κ = Fintype.card ι - d)

/-- The quotient of an arbitrary-scheme Grassmannian morphism has finite free neighborhoods. -/
theorem grassmannianSchemeImageQuotient_fixedFrames :
    ModuleSheafLocalFrames.HasFrames (ULift.{u} (Fin d))
      (grassmannianSchemeImageQuotient f b hκ) := by
  delta grassmannianSchemeImageQuotient
  exact @GrassmannianOpenChartDescent.quotientImageSheaf_fixedFrames
    R M ι κ _ _ _ _ _ d b hκ X f X.affineOpenCover.I₀
    (fun j ↦ X.affineOpenCover.X j) (fun _ ↦ inferInstance)
    (fun j ↦ schemeChartAlgebra f j) X.affineOpenCover.f (fun _ ↦ inferInstance)
    (schemeChartPoint f) (fun _ ↦ rfl) X.affineOpenCover.openCover.iSup_opensRange

end FLT.Mazur.GrassmannianChart

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianQuotientImageCocycle

/-!
# Descent of original Grassmannian quotient sheaves

An arbitrary morphism to the Grassmannian gives compatible quotient sheaves on
its affine open charts. The whole-overlap comparisons satisfy the geometric
refinement and cocycle hypotheses of module-sheaf gluing.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.GrassmannianOpenChartDescent
open GrassmannianChart GrassmannianOverlapAffineTransition
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

/-- Original affine quotient sheaves descend along their actual full image transitions. -/
@[irreducible] def quotientImageGluingData :
    ModuleSheafGluing.Data (fun j ↦ (i j).opensRange) :=
  ModuleSheafGluing.imageChartData (fun j ↦ Spec (.of (A j))) i
    (fun j ↦ grassmannianQuotientSheaf (ambientMorphismPoint (a j).val (a j).property))
    (quotientImageTransition b hκ f A i a h)
    (quotientImageTransition_cocycle_eval b hκ f A i a h)

/-- A single sheaf retaining the entire original quotient on every affine chart. -/
@[irreducible] def quotientImageSheaf : X.Modules :=
  (quotientImageGluingData b hκ f A i a h).glued

/-- Pullback to each original chart recovers its entire original quotient sheaf. -/
@[irreducible] def quotientImageSheafChartIso (j : J) :
    (pullback (i j)).obj (quotientImageSheaf b hκ f A i a h) ≅
      grassmannianQuotientSheaf (ambientMorphismPoint (a j).val (a j).property) := by
  delta quotientImageSheaf quotientImageGluingData
  exact ModuleSheafGluing.imageChartPullbackIso (fun j ↦ Spec (.of (A j))) i
    (fun j ↦ grassmannianQuotientSheaf (ambientMorphismPoint (a j).val (a j).property))
    (quotientImageTransition b hκ f A i a h)
    (quotientImageTransition_cocycle_eval b hκ f A i a h) j

end FLT.Mazur.GrassmannianOpenChartDescent

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianQuotientImageDescent
public import FLT.Mazur.ModuleSheafGluingTransportProjection
public import FLT.Mazur.ModuleSheafOpenImageProjectionRecovery

/-!
# Original chart projections of the descended Grassmannian quotient

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

open ModuleSheafGluing

/-- The actual descended quotient projects to the entire original chart pushforward. -/
@[irreducible] def quotientImageProjection (j : J) :
    quotientImageSheaf b hκ f A i a h ⟶ (pushforward (i j)).obj
      (grassmannianQuotientSheaf (ambientMorphismPoint (a j).val (a j).property)) := by
  delta quotientImageSheaf quotientImageGluingData imageChartData
  exact ambientProjection (fun j ↦ (i j).opensRange)
    (fun j ↦ imageModule (i j)
      (grassmannianQuotientSheaf (ambientMorphismPoint (a j).val (a j).property)))
    (fun j ↦ (pushforward (i j)).obj
      (grassmannianQuotientSheaf (ambientMorphismPoint (a j).val (a j).property)))
    (fun j ↦ imagePushforwardIso (i j)
      (grassmannianQuotientSheaf (ambientMorphismPoint (a j).val (a j).property)))
    (quotientImageTransition b hκ f A i a h)
    (quotientImageTransition_cocycle_eval b hκ f A i a h) j

/-- The actual original transitions identify the descended chart projections. -/
@[reassoc] theorem quotientImageProjection_transition (j k : J) :
    (quotientImageProjection b hκ f A i a h j).over
        ((i j).opensRange ⊓ (i k).opensRange) ≫
      (quotientImageTransition b hκ f A i a h j k).hom =
    (quotientImageProjection b hκ f A i a h k).over
      ((i j).opensRange ⊓ (i k).opensRange) := by
  delta quotientImageProjection quotientImageSheaf quotientImageGluingData imageChartData
  exact ambientProjection_transition (fun j ↦ (i j).opensRange)
    (fun j ↦ imageModule (i j)
      (grassmannianQuotientSheaf (ambientMorphismPoint (a j).val (a j).property)))
    (fun j ↦ (pushforward (i j)).obj
      (grassmannianQuotientSheaf (ambientMorphismPoint (a j).val (a j).property)))
    (fun j ↦ imagePushforwardIso (i j)
      (grassmannianQuotientSheaf (ambientMorphismPoint (a j).val (a j).property)))
    (quotientImageTransition b hκ f A i a h)
    (quotientImageTransition_cocycle_eval b hκ f A i a h) j k

/-- Chart recovery is the adjoint of the actual descended projection. -/
theorem quotientImageSheafChartIso_projection (j : J) :
    (quotientImageSheafChartIso b hκ f A i a h j).hom =
      (pullback (i j)).map (quotientImageProjection b hκ f A i a h j) ≫
        (ModuleSheafOverlapImageTransition.openCounitIso (i j)
          (grassmannianQuotientSheaf (ambientMorphismPoint (a j).val (a j).property))).hom := by
  delta quotientImageSheafChartIso quotientImageGluingData imageChartPullbackIso
    imageChartData quotientImageProjection quotientImageSheaf
  exact pullbackRecovery_projection (i j)
    (grassmannianQuotientSheaf (ambientMorphismPoint (a j).val (a j).property)) _ _ _ rfl

end FLT.Mazur.GrassmannianOpenChartDescent

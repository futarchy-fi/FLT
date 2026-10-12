/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianQuotientImageProjection
public import FLT.Mazur.GrassmannianAmbientChartConeCompatibility
public import FLT.Mazur.ModuleSheafGluingTransportLift

/-!
# The global ambient map into the descended Grassmannian quotient

The actual compatible adjoints lift from one global ambient sheaf. Each full
original chart component is recovered, and these components determine the lift.
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

/-- The actual original chart maps form a cone from the one global ambient sheaf. -/
@[irreducible] def quotientAmbientCone :
    AmbientCone (fun j ↦ (i j).opensRange)
      (fun j ↦ (pushforward (i j)).obj
        (grassmannianQuotientSheaf (ambientMorphismPoint (a j).val (a j).property)))
      (quotientImageTransition b hκ f A i a h)
      (S := grassmannianSchemeAmbient (M := M)
        (f ≫ ambientGrassmannianStructure R M κ d)) where
  app := quotientAmbientChartAdjoint f A i a h
  compatible := quotientAmbientChartAdjoint_transition b hκ f A i a h

/-- The global map from the original ambient sheaf into the full descended quotient. -/
@[irreducible] def quotientImageAmbientMap :
    grassmannianSchemeAmbient (M := M) (f ≫ ambientGrassmannianStructure R M κ d) ⟶
      quotientImageSheaf b hκ f A i a h := by
  delta quotientImageSheaf quotientImageGluingData imageChartData
  exact ambientLift (fun j ↦ (i j).opensRange)
    (fun j ↦ imageModule (i j)
      (grassmannianQuotientSheaf (ambientMorphismPoint (a j).val (a j).property)))
    (fun j ↦ (pushforward (i j)).obj
      (grassmannianQuotientSheaf (ambientMorphismPoint (a j).val (a j).property)))
    (fun j ↦ imagePushforwardIso (i j)
      (grassmannianQuotientSheaf (ambientMorphismPoint (a j).val (a j).property)))
    (quotientImageTransition b hκ f A i a h)
    (quotientImageTransition_cocycle_eval b hκ f A i a h)
    (quotientAmbientCone b hκ f A i a h)

/-- The global ambient map recovers every full original chart pushforward component. -/
@[reassoc] theorem quotientImageAmbientMap_projection (j : J) :
    quotientImageAmbientMap b hκ f A i a h ≫ quotientImageProjection b hκ f A i a h j =
      quotientAmbientChartAdjoint f A i a h j := by
  delta quotientImageAmbientMap quotientImageProjection quotientImageSheaf
    quotientImageGluingData imageChartData
  simpa only [quotientAmbientCone, id] using
    ambientLift_projection (fun j ↦ (i j).opensRange)
    (fun j ↦ imageModule (i j)
      (grassmannianQuotientSheaf (ambientMorphismPoint (a j).val (a j).property)))
    (fun j ↦ (pushforward (i j)).obj
      (grassmannianQuotientSheaf (ambientMorphismPoint (a j).val (a j).property)))
    (fun j ↦ imagePushforwardIso (i j)
      (grassmannianQuotientSheaf (ambientMorphismPoint (a j).val (a j).property)))
    (quotientImageTransition b hκ f A i a h)
    (quotientImageTransition_cocycle_eval b hκ f A i a h)
    (quotientAmbientCone b hκ f A i a h) j

/-- Every original chart component determines the global ambient map uniquely. -/
theorem quotientImageAmbientMap_unique
    (q : grassmannianSchemeAmbient (M := M) (f ≫ ambientGrassmannianStructure R M κ d) ⟶
      quotientImageSheaf b hκ f A i a h)
    (hq : ∀ j, q ≫ quotientImageProjection b hκ f A i a h j =
      quotientAmbientChartAdjoint f A i a h j) :
    q = quotientImageAmbientMap b hκ f A i a h := by
  delta quotientImageAmbientMap
  delta quotientImageProjection quotientImageSheaf quotientImageGluingData imageChartData at *
  apply ambientLift_unique (fun j ↦ (i j).opensRange)
    (fun j ↦ imageModule (i j)
      (grassmannianQuotientSheaf (ambientMorphismPoint (a j).val (a j).property)))
    (fun j ↦ (pushforward (i j)).obj
      (grassmannianQuotientSheaf (ambientMorphismPoint (a j).val (a j).property)))
    (fun j ↦ imagePushforwardIso (i j)
      (grassmannianQuotientSheaf (ambientMorphismPoint (a j).val (a j).property)))
    (quotientImageTransition b hκ f A i a h)
    (quotientImageTransition_cocycle_eval b hκ f A i a h)
    (quotientAmbientCone b hκ f A i a h)
  intro j
  simpa only [quotientAmbientCone, id] using hq j

/-- Pullback recovers the entire original quotient map on each original affine chart. -/
@[reassoc] theorem quotientImageAmbientMap_chart (j : J) :
    (pullback (i j)).map (quotientImageAmbientMap b hκ f A i a h) ≫
        (quotientImageSheafChartIso b hκ f A i a h j).hom =
      quotientAmbientChartMap f A i a h j := by
  rw [quotientImageSheafChartIso_projection, ← Functor.map_comp_assoc,
    quotientImageAmbientMap_projection, quotientAmbientChartAdjoint_recovery]

end FLT.Mazur.GrassmannianOpenChartDescent

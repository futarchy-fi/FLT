/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianAmbientChartConeMap
public import FLT.Mazur.GrassmannianSchemeQuotientRefinement

/-!
# Full coordinate recovery for the actual ambient chart maps

The common ambient source and every original quotient remain unchanged under
coordinate pullback. This supplies the overlap compatibility input for descent.
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


open SheafPullbackAmbientNormalization ModuleSheafOpenChartAdjoint

attribute [local irreducible] grassmannianAmbientSheafPullbackIso comparison

/-- Pulling an original chart map to a common open recovers its full quotient projection. -/
theorem quotientAmbientChartMap_coordinate (j : J) (U : X.Opens)
    (hj : U ≤ (i j).opensRange) :
    (comparison (coordinate (i j) U hj) (i j) U.ι (coordinate_comp (i j) U hj)).inv.app
        (grassmannianSchemeAmbient (M := M) (f ≫ ambientGrassmannianStructure R M κ d)) ≫
      (pullback (coordinate (i j) U hj)).map (quotientAmbientChartMap f A i a h j) =
    (grassmannianSchemeAmbientRefinementIso (M := M) U.ι
        (f ≫ ambientGrassmannianStructure R M κ d)
        (U.ι ≫ f ≫ ambientGrassmannianStructure R M κ d) rfl).hom ≫
          subopenProjection f A i a h j U hj := by
  delta quotientAmbientChartMap subopenProjection grassmannianSchemeQuotientMap
    grassmannianSchemeAmbientIso grassmannianSchemeAmbientRefinementIso
    grassmannianSchemeAmbient
  simpa only [chartIso, id, Iso.app_hom] using
    ambientChartMap_coordinate _ (i j) _ (originalChart_base f A i a h j) _ _ _
    (grassmannianAmbientSheafPullbackIso (M := M) (Algebra.ofId R (A j)))
    (grassmannianQuotientSheafMap (ambientMorphismPoint (a j).val (a j).property))
    (coordinate (i j) U hj) U.ι _ (coordinate_comp (i j) U hj) rfl
    (coordinate_base f A i a h j U hj)

/-- Every coordinate of the actual adjoint is the original normalized quotient map. -/
theorem quotientAmbientChartAdjoint_coordinate (j : J) (U : X.Opens)
    (hj : U ≤ (i j).opensRange) :
    (pullback U.ι).map (quotientAmbientChartAdjoint f A i a h j) ≫
        (ModuleSheafOverlapImageTransition.coordinateIso (coordinate (i j) U hj)
          (i j) U.ι (coordinate_comp (i j) U hj)
          (grassmannianQuotientSheaf (ambientMorphismPoint (a j).val (a j).property))).hom =
      (grassmannianSchemeAmbientRefinementIso (M := M) U.ι
        (f ≫ ambientGrassmannianStructure R M κ d)
        (U.ι ≫ f ≫ ambientGrassmannianStructure R M κ d) rfl).hom ≫
          subopenProjection f A i a h j U hj := by
  delta quotientAmbientChartAdjoint
  rw [chartAdjoint_coordinate]
  exact quotientAmbientChartMap_coordinate f A i a h j U hj

end FLT.Mazur.GrassmannianOpenChartDescent

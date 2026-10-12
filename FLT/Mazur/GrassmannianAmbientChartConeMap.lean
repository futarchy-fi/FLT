/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianOpenChartProjection
public import FLT.Mazur.ModuleSheafOpenChartAdjoint
public import FLT.Mazur.SheafPullbackAmbientChartMap

/-!
# Actual maps from the global ambient sheaf to chart pushforwards

The base comparison and the original full quotient construct every chart map.
Adjunction then gives maps with one common global ambient source.
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

omit [∀ j, IsOpenImmersion (i j)] in
include h in
/-- Every original affine chart retains the common global base morphism. -/
theorem originalChart_base (j : J) :
    i j ≫ f ≫ ambientGrassmannianStructure R M κ d = Spec.algebraMap R (A j) := by
  rw [← Category.assoc, h j, (a j).property]

/-- The entire original quotient map on an affine chart of the source scheme. -/
@[irreducible] def quotientAmbientChartMap (j : J) :
    (pullback (i j)).obj
        (grassmannianSchemeAmbient (M := M) (f ≫ ambientGrassmannianStructure R M κ d)) ⟶
      grassmannianQuotientSheaf (ambientMorphismPoint (a j).val (a j).property) := by
  unfold grassmannianSchemeAmbient
  exact ambientChartMap _ (i j) _ (originalChart_base f A i a h j) _ _ _
    (grassmannianAmbientSheafPullbackIso (M := M) (Algebra.ofId R (A j)))
    (grassmannianQuotientSheafMap (ambientMorphismPoint (a j).val (a j).property))

/-- A map from the single global ambient sheaf into each original chart pushforward. -/
@[irreducible] def quotientAmbientChartAdjoint (j : J) :
    grassmannianSchemeAmbient (M := M) (f ≫ ambientGrassmannianStructure R M κ d) ⟶
      (pushforward (i j)).obj
        (grassmannianQuotientSheaf (ambientMorphismPoint (a j).val (a j).property)) :=
  chartAdjoint (i j) (quotientAmbientChartMap f A i a h j)

/-- The actual adjoint retains the full original chart quotient map. -/
@[reassoc] theorem quotientAmbientChartAdjoint_recovery (j : J) :
    (pullback (i j)).map (quotientAmbientChartAdjoint f A i a h j) ≫
        (ModuleSheafOverlapImageTransition.openCounitIso (i j)
          (grassmannianQuotientSheaf (ambientMorphismPoint (a j).val (a j).property))).hom =
      quotientAmbientChartMap f A i a h j := by
  unfold quotientAmbientChartAdjoint
  exact chartAdjoint_recovery _ _

end FLT.Mazur.GrassmannianOpenChartDescent

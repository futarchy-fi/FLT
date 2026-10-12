/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianQuotientImageAmbientMap
public import FLT.Mazur.GrassmannianAmbientChartNormalization
public import FLT.Mazur.GrassmannianSheafQuotientTest

/-!
# Original affine tests of the actual quotient image

The inverse of each original chart comparison identifies the actual descended
ambient epimorphism with the whole original affine test projection.
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

/-- The inverse image-chart comparison retains the whole original affine test projection. -/
theorem quotientImageSheafChartIso_inv_projection (j : J) :
    grassmannianQuotientSheafMap (ambientMorphismPoint (a j).val (a j).property) ≫
        (quotientImageSheafChartIso b hκ f A i a h j).inv =
      sheafQuotientTestMap (f ≫ ambientGrassmannianStructure R M κ d)
        (quotientImageAmbientMap b hκ f A i a h) (i j)
        (originalChart_base f A i a h j) := by
  unfold sheafQuotientTestMap
  apply (cancel_epi (grassmannianSchemeAmbientTestIso (M := M)
    (f ≫ ambientGrassmannianStructure R M κ d) (i j)
    (originalChart_base f A i a h j)).hom).mp
  apply (cancel_mono (quotientImageSheafChartIso b hκ f A i a h j).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_assoc]
  rw [quotientImageAmbientMap_chart, quotientAmbientChartMap_normalized]

end FLT.Mazur.GrassmannianOpenChartDescent

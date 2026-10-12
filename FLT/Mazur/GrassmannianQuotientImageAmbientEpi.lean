/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianQuotientImageAmbientMap
public import FLT.Mazur.ModuleSheafOpenCoverEpi

/-!
# Surjectivity of the original global Grassmannian quotient map

Each original quotient is epi. The proved chart recovery and the actual open
cover therefore make the global ambient map an epimorphism.
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

/-- The full map on each original affine chart is epi. -/
instance quotientAmbientChartMap_epi (j : J) :
    Epi (quotientAmbientChartMap f A i a h j) := by
  delta quotientAmbientChartMap SheafPullbackAmbientNormalization.ambientChartMap
    grassmannianSchemeAmbient
  dsimp only [id]
  infer_instance

/-- Pullback of the actual global map to any original affine chart is epi. -/
instance quotientImageAmbientMap_pullback_epi (j : J) :
    Epi ((pullback (i j)).map (quotientImageAmbientMap b hκ f A i a h)) := by
  rw [← epi_comp_iff_of_isIso _ (quotientImageSheafChartIso b hκ f A i a h j).hom,
    quotientImageAmbientMap_chart]
  infer_instance

/-- On a covering family the actual global ambient map is an epimorphism. -/
theorem quotientImageAmbientMap_epi (hc : ⨆ j, (i j).opensRange = ⊤) :
    Epi (quotientImageAmbientMap b hκ f A i a h) :=
  ModuleSheafOpenImmersionLocalHom.epi_of_openCover (fun j ↦ Spec (.of (A j))) i hc _

end FLT.Mazur.GrassmannianOpenChartDescent

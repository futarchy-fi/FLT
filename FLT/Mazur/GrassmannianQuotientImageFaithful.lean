/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianQuotientImageAmbientMap
public import FLT.Mazur.GrassmannianAmbientChartNormalization
public import FLT.Mazur.GrassmannianSchemeQuotientFaithful
public import FLT.Mazur.QuotientChartComparison

/-!
# Faithfulness of the actual descended ambient quotient

A global isomorphism preserving the full ambient projection recovers every
original chart point. On a covering family it determines the entire original
scheme morphism, with the original base map retained.
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

variable (g : X ⟶ ambientGrassmannianScheme R M κ d)
  (a' : ∀ j, {a : Spec (.of (A j)) ⟶ ambientGrassmannianScheme R M κ d //
    a ≫ ambientGrassmannianStructure R M κ d = Spec.algebraMap R (A j)})
  (h' : ∀ j, i j ≫ g = (a' j).val)
  (hβ : f ≫ ambientGrassmannianStructure R M κ d =
    g ≫ ambientGrassmannianStructure R M κ d)
variable (e : quotientImageSheaf b hκ f A i a h ≅ quotientImageSheaf b hκ g A i a' h')
  (he : quotientImageAmbientMap b hκ f A i a h ≫ e.hom =
    (eqToIso (congrArg (grassmannianSchemeAmbient (M := M)) hβ)).hom ≫
      quotientImageAmbientMap b hκ g A i a' h')

include he in
/-- A full global quotient comparison recovers the entire original point on each chart. -/
theorem quotientImagePoint_eq_of_iso (j : J) :
    ambientMorphismPoint (a j).val (a j).property =
      ambientMorphismPoint (a' j).val (a' j).property := by
  apply grassmannianPoint_eq_of_quotientSheafIso _ _
    ((quotientImageSheafChartIso b hκ f A i a h j).symm ≪≫
      (pullback (i j)).mapIso e ≪≫ quotientImageSheafChartIso b hκ g A i a' h' j)
  refine QuotientChartComparison.projection (pullback (i j))
    (quotientImageAmbientMap b hκ f A i a h) (quotientImageAmbientMap b hκ g A i a' h')
    (eqToIso (congrArg (grassmannianSchemeAmbient (M := M)) hβ)) e
    (grassmannianSchemeAmbientTestIso _ (i j) (originalChart_base f A i a h j))
    (grassmannianSchemeAmbientTestIso _ (i j) (originalChart_base g A i a' h' j))
    (quotientImageSheafChartIso b hκ f A i a h j)
    (quotientImageSheafChartIso b hκ g A i a' h' j) _ _ he ?_ ?_ ?_
  · exact grassmannianSchemeAmbientTestIso_congr _ _ hβ _ _ _
  · rw [quotientImageAmbientMap_chart, quotientAmbientChartMap_normalized]
  · rw [quotientImageAmbientMap_chart, quotientAmbientChartMap_normalized]

include he in
/-- A covering family makes the actual full descended quotient faithful to its scheme map. -/
theorem quotientImageMorphism_eq_of_iso
    (hc : ∀ x : X, ∃ j, x ∈ Set.range (i j)) : f = g := by
  let C : X.OpenCover :=
    { I₀ := J
      X j := Spec (.of (A j))
      f := i
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨hc, fun _ ↦ inferInstance⟩ }
  apply C.hom_ext
  intro j
  change i j ≫ f = i j ≫ g
  rw [h j, h' j]
  rw [← ambientMorphismPoint_classifies (a j).val (a j).property b hκ,
    ← ambientMorphismPoint_classifies (a' j).val (a' j).property b hκ,
    quotientImagePoint_eq_of_iso b hκ f A i a h g a' h' hβ e he j]

end FLT.Mazur.GrassmannianOpenChartDescent

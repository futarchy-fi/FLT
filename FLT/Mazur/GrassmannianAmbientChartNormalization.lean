/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianAmbientChartConeMap
public import FLT.Mazur.GrassmannianSchemeQuotientTest

/-!
# Normalizing the full original affine quotient chart

The actual chart map from the global ambient sheaf is its original coefficient
quotient projection after the canonical ambient test comparison.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.GrassmannianOpenChartDescent
open GrassmannianChart SheafPullbackAmbientNormalization
universe u
variable {R M κ : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype κ] {d : ℕ}
variable {X : Scheme.{u}} (f : X ⟶ ambientGrassmannianScheme R M κ d)
variable {J : Type u} (A : J → Type u) [∀ j, CommRing (A j)] [∀ j, Algebra R (A j)]
  (i : ∀ j, Spec (.of (A j)) ⟶ X)
variable (a : ∀ j, {a : Spec (.of (A j)) ⟶ ambientGrassmannianScheme R M κ d //
  a ≫ ambientGrassmannianStructure R M κ d = Spec.algebraMap R (A j)})
  (h : ∀ j, i j ≫ f = (a j).val)
attribute [local irreducible] Scheme.Modules.pullback grassmannianQuotientSheaf
  grassmannianAmbientSheafPullbackIso SheafPullbackPathComparison.comparison

/-- The actual chart map retains exactly the full original coefficient projection. -/
theorem quotientAmbientChartMap_normalized (j : J) :
    quotientAmbientChartMap f A i a h j =
      (grassmannianSchemeAmbientTestIso
        (f ≫ ambientGrassmannianStructure R M κ d) (i j)
        (originalChart_base f A i a h j)).hom ≫
      grassmannianQuotientSheafMap (ambientMorphismPoint (a j).val (a j).property) := by
  unfold quotientAmbientChartMap grassmannianSchemeAmbientTestIso
    SheafPullbackAmbientNormalization.ambientChartMap testIso grassmannianSchemeAmbient
  dsimp only [id, Iso.trans_hom, Iso.app_hom]
  exact (Category.assoc (obj := (Spec (.of (A j))).Modules) _ _ _).symm

end FLT.Mazur.GrassmannianOpenChartDescent

namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A M : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M]
variable {X : Scheme.{u}} (β β' : X ⟶ Spec (.of R)) (hβ : β = β')
  (i : Spec (.of A) ⟶ X) (hi : i ≫ β = Spec.algebraMap R A)
  (hi' : i ≫ β' = Spec.algebraMap R A)
attribute [local irreducible] Scheme.Modules.pullback

/-- Equal original base maps induce the same full affine ambient comparison. -/
@[reassoc] theorem grassmannianSchemeAmbientTestIso_congr :
    (pullback i).map (eqToIso (congrArg (grassmannianSchemeAmbient (M := M)) hβ)).hom ≫
        (grassmannianSchemeAmbientTestIso β' i hi').hom =
      (grassmannianSchemeAmbientTestIso β i hi).hom := by
  subst β'
  exact (congrArg (fun t ↦ t ≫ (grassmannianSchemeAmbientTestIso β i hi).hom)
    ((pullback i).map_id _)).trans (Category.id_comp _)

end FLT.Mazur.GrassmannianChart

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianQuotientImageAmbientEpi
public import FLT.Mazur.ModuleSheafQuotientComparisonGluing

/-!
# Recovering a global quotient from its original affine charts

The actual descended ambient epimorphism recovers any global quotient with the
same original local projections. The comparison and its inverse are constructed
by gluing; overlap compatibility is forced by the full ambient projection.
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

open ModuleSheafQuotientComparisonGluing
variable (hc : ∀ x : X, ∃ j, x ∈ Set.range (i j))
variable (P : X.Modules)
  (p : grassmannianSchemeAmbient (M := M)
    (f ≫ ambientGrassmannianStructure R M κ d) ⟶ P)
variable (e : ∀ j, grassmannianQuotientSheaf
    (ambientMorphismPoint (a j).val (a j).property) ≅ (pullback (i j)).obj P)
  (he : ∀ j, quotientAmbientChartMap f A i a h j ≫ (e j).hom = (pullback (i j)).map p)

/-- The original chart identifications construct an actual global quotient isomorphism. -/
@[irreducible] def quotientImageRecoveryIso : quotientImageSheaf b hκ f A i a h ≅ P := by
  let _ := quotientImageAmbientMap_epi b hκ f A i a h
    (ModuleSheafOpenImmersionGluing.iSup_opensRange (fun j ↦ Spec (.of (A j))) i hc)
  exact quotientComparisonIso (fun j ↦ Spec (.of (A j))) i
    (quotientImageAmbientMap b hκ f A i a h) p
    (fun j ↦ (quotientImageSheafChartIso b hκ f A i a h j).hom ≫ (e j).hom)
    (fun j ↦ by rw [← Category.assoc, quotientImageAmbientMap_chart, he j]) hc
    (fun _ ↦ inferInstance)

/-- Recovery preserves the entire original global ambient projection. -/
@[reassoc] theorem quotientImageRecoveryIso_projection :
    quotientImageAmbientMap b hκ f A i a h ≫
        (quotientImageRecoveryIso b hκ f A i a h hc P p e he).hom = p := by
  let _ := quotientImageAmbientMap_epi b hκ f A i a h
    (ModuleSheafOpenImmersionGluing.iSup_opensRange (fun j ↦ Spec (.of (A j))) i hc)
  delta quotientImageRecoveryIso
  exact quotientComparisonIso_projection _ _ _ _ _ _ _ _

/-- The inverse recovers the actual constructed ambient quotient map. -/
@[reassoc] theorem quotientImageRecoveryIso_inv_projection :
    p ≫ (quotientImageRecoveryIso b hκ f A i a h hc P p e he).inv =
      quotientImageAmbientMap b hκ f A i a h := by
  have hh := congrArg
    (fun t ↦ t ≫ (quotientImageRecoveryIso b hκ f A i a h hc P p e he).inv)
    (quotientImageRecoveryIso_projection b hκ f A i a h hc P p e he)
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hh.symm

end FLT.Mazur.GrassmannianOpenChartDescent

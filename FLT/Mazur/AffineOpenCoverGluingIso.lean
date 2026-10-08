/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineOpenCoverComparisonGluing

/-!
# Gluing a refinement-compatible affine family of isomorphisms

A natural family on affine tests glues on any affine open cover. The global
isomorphism recovers each prescribed comparison as an actual pullback map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
open FLT.Mazur.AffineIteratedPullbackSections
universe u
namespace FLT.Mazur.AffineOpenCoverCommonRefinement
variable {X : Scheme.{u}} (U : X.AffineOpenCover) {P Q : X.Modules}
variable (a : ∀ {A : CommRingCat.{u}} (f : Spec A ⟶ X),
  (pullback f).obj P ⟶ (pullback f).obj Q)
variable (ha : ∀ {A B : CommRingCat.{u}} (f : Spec A ⟶ X)
  (g : Spec B ⟶ X) (α : A ⟶ B) (w : Spec.map α ≫ f = g),
  (pullback (Spec.map α)).map (a f) ≫ (compositeIso (Spec.map α) f g w Q).hom =
    (compositeIso (Spec.map α) f g w P).hom ≫ a g)
variable (hiso : ∀ i, IsIso (a (U.f i)))

/-- Every affine open cover is jointly surjective. -/
theorem jointly_surjective (x : X) : ∃ i, x ∈ Set.range (U.f i) :=
  ⟨U.idx x, U.covers x⟩

/-- Glue invertible affine comparisons using their refinement equations. -/
def comparisonIso : P ≅ Q :=
  ModuleSheafOpenImmersionGluing.glueIso (M := P) (N := Q)
    (fun i ↦ Spec (U.X i)) U.f (jointly_surjective U)
    (fun i ↦ a (U.f i)) (compatible_of_affine_refinements U a ha) hiso

/-- Pullback of the glued comparison recovers the given affine map exactly. -/
theorem comparisonIso_restrict (i : U.I₀) :
    (pullback (U.f i)).map (comparisonIso U a ha hiso).hom = a (U.f i) :=
  ModuleSheafOpenImmersionGluing.pullback_glue (M := P) (N := Q)
    (fun i ↦ Spec (U.X i)) U.f (jointly_surjective U)
    (fun i ↦ a (U.f i)) (compatible_of_affine_refinements U a ha) i

end FLT.Mazur.AffineOpenCoverCommonRefinement

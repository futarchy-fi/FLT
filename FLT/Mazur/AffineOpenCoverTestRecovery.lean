/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineOpenCoverTestRefinement
public import FLT.Mazur.SheafPullbackPathComparison
/-!
# Recovery of glued comparisons on arbitrary affine tests

An affine family compatible with refinement is determined on every affine test by its
values on a single open cover. The proof uses a constructed pullback affine cover.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
open FLT.Mazur.AffineIteratedPullbackSections
universe u
namespace FLT.Mazur.AffineOpenCoverCommonRefinement
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] compositeIso

private theorem pullback_square {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (k : X ⟶ Z) (w : f ≫ g = k) {P Q : Z.Modules} (e : P ⟶ Q) :
    (pullback f).map ((pullback g).map e) ≫ (compositeIso f g k w Q).hom =
      (compositeIso f g k w P).hom ≫ (pullback k).map e := by
  unfold compositeIso
  exact (SheafPullbackPathComparison.comparison f g k w).hom.naturality e

variable {X : Scheme.{u}} (U : X.AffineOpenCover) {P Q : X.Modules}
variable (a : ∀ {A : CommRingCat.{u}} (f : Spec A ⟶ X),
  (pullback f).obj P ⟶ (pullback f).obj Q)
variable (ha : ∀ {A B : CommRingCat.{u}} (f : Spec A ⟶ X)
  (g : Spec B ⟶ X) (α : A ⟶ B) (w : Spec.map α ≫ f = g),
  (pullback (Spec.map α)).map (a f) ≫ (compositeIso (Spec.map α) f g w Q).hom =
    (compositeIso (Spec.map α) f g w P).hom ≫ a g)

include ha in
/-- Recovery on the original affine cover implies recovery on every affine test. -/
theorem recover_on_affine_test (e : P ⟶ Q)
    (he : ∀ i, (pullback (U.f i)).map e = a (U.f i))
    {A : CommRingCat.{u}} (f : Spec A ⟶ X) : (pullback f).map e = a f := by
  apply ModuleSheafOpenImmersionGluing.hom_ext
    (fun i ↦ Spec ((testCover U f).X i)) (testCover U f).f (testCover_covers U f)
  intro i
  have ht : (pullback (testMap U f i)).map e = a (testMap U f i) := by
    apply (cancel_epi (compositeIso (Spec.map (testTarget U f i))
      (U.f (testIndex U f i)) (testMap U f i) (testTarget_over U f i) P).hom).mp
    rw [← pullback_square, he]
    exact ha _ _ _ (testTarget_over U f i)
  rw [← testSource_spec U f i]
  apply (cancel_mono (compositeIso (Spec.map (testSource U f i)) f
    (testMap U f i) (testSource_over U f i) Q).hom).mp
  rw [pullback_square, ht]
  exact (ha _ _ _ (testSource_over U f i)).symm

/-- The glued affine isomorphism recovers the prescribed map on arbitrary affine tests. -/
theorem comparisonIso_test (hiso : ∀ i, IsIso (a (U.f i)))
    {A : CommRingCat.{u}} (f : Spec A ⟶ X) :
    (pullback f).map (comparisonIso U a ha hiso).hom = a f :=
  recover_on_affine_test U a ha (comparisonIso U a ha hiso).hom
    (comparisonIso_restrict U a ha hiso) f

end FLT.Mazur.AffineOpenCoverCommonRefinement

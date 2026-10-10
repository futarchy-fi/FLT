/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafRefinementGluing
public import FLT.Mazur.AffineOpenCoverCommonRefinement

/-!
# Compatibility of affine map families on a scheme

An abstract family of module maps compatible with affine refinement is
compatible on the given affine cover. Keeping the sheaves abstract isolates
the geometric cover argument from effective descent constructions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
open FLT.Mazur.AffineIteratedPullbackSections
universe u
namespace FLT.Mazur.AffineOpenCoverCommonRefinement
attribute [local irreducible] compositeIso ModuleSheafOpenImmersionGluing.Compatible
  commonCover commonMap
variable {X : Scheme.{u}} (U : X.AffineOpenCover) {P Q : X.Modules}
variable (a : ∀ {A : CommRingCat.{u}} (f : Spec A ⟶ X),
  (pullback f).obj P ⟶ (pullback f).obj Q)
variable (ha : ∀ {A B : CommRingCat.{u}} (f : Spec A ⟶ X)
  (g : Spec B ⟶ X) (α : A ⟶ B) (w : Spec.map α ≫ f = g),
  (pullback (Spec.map α)).map (a f) ≫ (compositeIso (Spec.map α) f g w Q).hom =
    (compositeIso (Spec.map α) f g w P).hom ≫ a g)

include ha in
/-- The affine chart maps are compatible on their entire open intersections. -/
theorem compatible_of_affine_refinements :
    ModuleSheafOpenImmersionGluing.Compatible (M := P) (N := Q)
      (fun i ↦ Spec (U.X i)) U.f
      (fun i ↦ a (U.f i)) :=
  ModuleSheafOpenImmersionGluing.compatible_of_geometric_refinements (M := P) (N := Q)
    (fun i ↦ Spec (U.X i)) U.f
    (fun i ↦ a (U.f i))
    (fun i j ↦ (commonCover (U.f i) (U.f j)).I₀)
    (fun i j k ↦ Spec ((commonCover (U.f i) (U.f j)).X k))
    (fun i j k ↦ commonMap (U.f i) (U.f j) k)
    (fun i j k ↦ Spec.map (commonLeft (U.f i) (U.f j) k))
    (fun i j k ↦ Spec.map (commonRight (U.f i) (U.f j) k))
    (fun i j k ↦ commonLeft_over (U.f i) (U.f j) k)
    (fun i j k ↦ commonRight_over (U.f i) (U.f j) k)
    (fun i j x hx ↦ commonMap_covers (U.f i) (U.f j) x hx)
    (fun i j k ↦ a (commonMap (U.f i) (U.f j) k))
    (fun i j k ↦ ha _ _ _ (commonLeft_over (U.f i) (U.f j) k))
    (fun i j k ↦ ha _ _ _ (commonRight_over (U.f i) (U.f j) k))

end FLT.Mazur.AffineOpenCoverCommonRefinement

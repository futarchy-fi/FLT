/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PrincipalOpenTensorPullback

/-!
# Cartesian intersections of tensor charts

An entire integral intersection described by two principal boundary maps
remains the entire intersection after extension of coefficients.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
namespace FLT.Mazur.TensorOpenChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
  {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]
  (x : A) (y : B) (z : C)
  (e : Localization.Away x ≃ₐ[R] Localization.Away y)
  (g : Localization.Away x ≃ₐ[R] Localization.Away z)
local notation "E" => PrincipalOpenTensor.transitionIso S x y e
local notation "G" => PrincipalOpenTensor.transitionIso S x z g

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
  (i : Spec (.of B) ⟶ X) (j : Spec (.of C) ⟶ X)
  (hi : i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B)))
  (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R C)))
  (H : IsPullback
    (Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away y))))
    (Spec.map (CommRingCat.ofHom g.symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away z)))) i j)

include H in
/-- No additional intersection appears between the actual tensor charts. -/
theorem common_boundary_isPullback :
    IsPullback ((E).inv ≫ PrincipalOpenTensor.inclusion S y)
      ((G).inv ≫ PrincipalOpenTensor.inclusion S z)
      (chart f i hi) (chart f j hj) := by
  have h := (PrincipalOpenTensor.transition_inv_isPullback S x y e).paste_vert H
  rw [← chart_snd f i hi] at h
  have hp : ((G).inv ≫ PrincipalOpenTensor.inclusion S z) ≫ projection =
      PrincipalOpenTensor.projection S x ≫
        (Spec.map (CommRingCat.ofHom g.symm.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away z)))) := by
    rw [Category.assoc, PrincipalOpenTensor.inclusion_projection,
      transition_inv_projection_assoc]
  rw [← hp] at h
  exact h.of_bot (by
    simpa only [Category.assoc] using common_boundary S x y z e g f i j hi hj
      (by simpa only [Category.assoc] using H.w)) (chart_isPullback f j hj)

end FLT.Mazur.TensorOpenChart

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PrincipalOpenTensorGeometry

/-!
# Integral principal-overlap squares inside a tensor atlas

An original gluing square remains a gluing square inside the actual
categorical coefficient pullback, on the entire localized tensor algebras.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.TensorOpenChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
  {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
  (i : Spec (.of A) ⟶ X) (j : Spec (.of B) ⟶ X)
  (hi : i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)))
  (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B)))
  (x : A) (y : B) (e : Localization.Away x ≃ₐ[R] Localization.Away y)
  (h : Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away x))) ≫ i =
      Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away y))) ≫ j)

include h in
/-- Base change retains the full principal-overlap gluing square inside the atlas. -/
@[reassoc] theorem chart_overlap :
    (PrincipalOpenTensor.transitionIso S x y e).hom ≫
      PrincipalOpenTensor.inclusion S x ≫ chart f i hi =
        PrincipalOpenTensor.inclusion S y ≫ chart f j hj := by
  apply pullback.hom_ext
  · simp only [Category.assoc, chart_fst, PrincipalOpenTensor.inclusion_structure,
      PrincipalOpenTensor.transitionIso_structure]
  · simp only [Category.assoc, chart_snd]
    rw [PrincipalOpenTensor.inclusion_projection_assoc,
      PrincipalOpenTensor.transitionIso_projection_assoc, h,
      PrincipalOpenTensor.inclusion_projection_assoc]

end FLT.Mazur.TensorOpenChart

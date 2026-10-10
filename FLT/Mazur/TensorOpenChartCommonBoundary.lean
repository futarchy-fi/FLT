/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.TensorOpenChartOverlap

/-!
# Tensor charts with a common original principal boundary

Two charts identified with the same integral principal boundary retain that
identification after coefficient extension. Both comparison maps use the
actual tensor transitions, including their original projections.
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

/-- The inverse tensor transition keeps the reverse integral boundary projection. -/
@[reassoc] theorem transition_inv_projection :
    (E).inv ≫ PrincipalOpenTensor.projection S y =
      PrincipalOpenTensor.projection S x ≫ Spec.map (CommRingCat.ofHom e.symm.toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (PrincipalOpenTensor.transition_symm_coefficient S x y e)

/-- The reverse boundary transition retains all extended coefficients. -/
@[reassoc] theorem transition_inv_structure :
    (E).inv ≫ Spec.map (CommRingCat.ofHom
      (algebraMap S (Localization.Away ((1 : S) ⊗ₜ[R] y)))) =
        Spec.map (CommRingCat.ofHom
          (algebraMap S (Localization.Away ((1 : S) ⊗ₜ[R] x)))) := by
  apply (cancel_epi (E).hom).mp
  rw [Iso.hom_inv_id_assoc]
  exact (PrincipalOpenTensor.transitionIso_structure S x y e).symm

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
  (i : Spec (.of B) ⟶ X) (j : Spec (.of C) ⟶ X)
  (hi : i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B)))
  (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R C)))
  (h : Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away y))) ≫ i =
    Spec.map (CommRingCat.ofHom g.symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away z))) ≫ j)

include h in
/-- The two whole tensor boundaries agree inside the actual coefficient pullback. -/
@[reassoc] theorem common_boundary :
    (E).inv ≫ PrincipalOpenTensor.inclusion S y ≫ chart f i hi =
      (G).inv ≫ PrincipalOpenTensor.inclusion S z ≫ chart f j hj := by
  apply pullback.hom_ext
  · simp only [Category.assoc, chart_fst, PrincipalOpenTensor.inclusion_structure,
      transition_inv_structure]
  · simp only [Category.assoc, chart_snd]
    rw [PrincipalOpenTensor.inclusion_projection_assoc,
      transition_inv_projection_assoc, h,
      PrincipalOpenTensor.inclusion_projection_assoc, transition_inv_projection_assoc]

end FLT.Mazur.TensorOpenChart

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# The spectrum of an overlap product map

The algebra map from a tensor product to an overlap is exactly the geometric
map into the product of its two charts. Closedness therefore transfers
between these two descriptions without an extra geometric hypothesis.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.Approximation

universe u

variable {R B C D : Type u} [CommRing R] [CommRing B] [CommRing C] [CommRing D]
  [Algebra R B] [Algebra R C] [Algebra R D]
  (f : B →ₐ[R] D) (g : C →ₐ[R] D)

/-- The two restrictions to an overlap agree over the affine base. -/
theorem affineProductMap_condition :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R B)) =
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R C)) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (f.comp_algebraMap.trans g.comp_algebraMap.symm)

/-- The product coordinate map gives the geometric lift into the chart product. -/
theorem affineProductMap_spec :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap f g).toRingHom) ≫
      (pullbackSpecIso R B C).inv =
    pullback.lift (Spec.map (CommRingCat.ofHom f.toRingHom))
      (Spec.map (CommRingCat.ofHom g.toRingHom)) (affineProductMap_condition f g) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackSpecIso_inv_fst, pullback.lift_fst,
      ← Spec.map_comp]
    congr 1
    ext b
    exact Algebra.TensorProduct.productMap_left_apply f g b
  · simp only [Category.assoc, pullbackSpecIso_inv_snd, pullback.lift_snd,
      ← Spec.map_comp]
    congr 1
    ext c
    exact Algebra.TensorProduct.productMap_right_apply f g c

/-- Closedness of the geometric overlap map is equivalent to that of its coordinates. -/
theorem affineProductMap_isClosedImmersion_iff :
    IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap f g).toRingHom)) ↔
    IsClosedImmersion (pullback.lift (Spec.map (CommRingCat.ofHom f.toRingHom))
      (Spec.map (CommRingCat.ofHom g.toRingHom)) (affineProductMap_condition f g)) := by
  rw [← affineProductMap_spec,
    MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion]

/-- Actual affine intersections in a separated scheme are closed in their chart products. -/
theorem affineProductMap_isClosedImmersion_of_isPullback {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) [IsSeparated p]
    (i : Spec (.of B) ⟶ X) (j : Spec (.of C) ⟶ X)
    (hp : IsPullback (Spec.map (CommRingCat.ofHom f.toRingHom))
      (Spec.map (CommRingCat.ofHom g.toRingHom)) i j)
    (hi : i ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (hj : j ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R C))) :
    IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.productMap f g).toRingHom)) := by
  rw [affineProductMap_isClosedImmersion_iff]
  have he : pullback.lift (Spec.map (CommRingCat.ofHom f.toRingHom))
      (Spec.map (CommRingCat.ofHom g.toRingHom)) (affineProductMap_condition f g) =
      hp.isoPullback.hom ≫ pullback.mapDesc i j p ≫ (pullback.congrHom hi hj).hom := by
    apply pullback.hom_ext <;> simp
  rw [he]
  infer_instance

end FLT.Mazur.Approximation

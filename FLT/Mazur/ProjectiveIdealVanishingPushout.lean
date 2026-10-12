/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveIdealVanishingEquiv
public import Mathlib.Algebra.Category.Ring.Constructions

/-!
# Coefficient ideals across an actual ring pushout

The tensor-coordinate result descends along the canonical pushout isomorphism.
This formulation applies directly to cartesian affine charts and their
restriction maps.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.ProjectiveIdealVanishing
variable (R A B D : Type) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra R D] [Algebra A D] [Algebra B D]
  [IsScalarTower R A D] [IsScalarTower R B D] [Algebra.IsPushout R A B D]
  [Module.Projective R B] [Module.Projective A D] (J : Ideal B)

/-- The actual pushout extension has precisely the extended coefficient ideal. -/
theorem ideal_pushout :
    ideal A D (J.map (algebraMap B D)) = (ideal R B J).map (algebraMap R A) := by
  let e := Algebra.IsPushout.equiv R A B D
  have he :
      (J.map (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map
        e.toRingHom = J.map (algebraMap B D) := by
    rw [Ideal.map_map]
    congr 1
    ext b
    simp [e, Algebra.IsPushout.equiv_tmul]
  rw [← he, ideal_equiv, ideal_extendedIdeal]

end FLT.Mazur.ProjectiveIdealVanishing

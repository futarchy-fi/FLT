/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ReesRelativeNaturality
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Localization of relative Rees tensor rings

Localizing the chart ring localizes its tensor product with the unchanged
base Rees algebra. The algebra structure is the actual relative map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

namespace FLT.Mazur.Rees

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] (I : Ideal R) (f : S →ₐ[R] T)

/-- The target relative tensor ring is an algebra via the actual chart map. -/
@[instance_reducible]
def relativeMapAlgebra : Algebra (S ⊗[R] reesAlgebra I) (T ⊗[R] reesAlgebra I) :=
  (relativeAlgebraMap I f).toRingHom.toAlgebra

/-- Relative Rees tensor rings localize at exactly the chart denominators. -/
theorem relativeAlgebraMap_isLocalization (r : S)
    (h : let _ := f.toRingHom.toAlgebra; IsLocalization.Away r T) :
    let _ := relativeMapAlgebra I f
    IsLocalization.Away (Algebra.algebraMap S (S ⊗[R] reesAlgebra I) r)
      (T ⊗[R] reesAlgebra I) := by
  let _ := f.toRingHom.toAlgebra
  let _ : IsScalarTower R S T := .of_algebraMap_eq' f.comp_algebraMap.symm
  let _ := h
  let _ := relativeMapAlgebra I f
  let _ : IsScalarTower S (S ⊗[R] reesAlgebra I)
      (T ⊗[R] reesAlgebra I) := by
    refine ⟨fun s p q ↦ ?_⟩
    change relativeAlgebraMap I f (s • p) * q = s • (relativeAlgebraMap I f p * q)
    rw [← smul_mul_assoc]
    congr 1
    induction p using TensorProduct.inductionOn with
    | add p q hp hq => simp only [smul_add, map_add, hp, hq]
    | tmul t p =>
      change f (s * t) ⊗ₜ[R] p = (f s * f t) ⊗ₜ[R] p
      rw [map_mul]
  have ht := IsLocalization.tensorProduct_tensorProduct R (reesAlgebra I)
    (Submonoid.powers r) T (by
      ext p
      change f 1 ⊗ₜ[R] p = 1 ⊗ₜ[R] p
      rw [map_one])
  rw [Algebra.algebraMapSubmonoid_powers] at ht
  exact ht

end FLT.Mazur.Rees

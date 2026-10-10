/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.StandardSmoothCoefficientFiber
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Finite fiber support after arbitrary ambient localization

An ambient localization need not retain finiteness of a closed family over
the base. Its actual field-fiber quotient is nevertheless Artinian: it is a
localization of the original finite-dimensional quotient. The proof keeps
the full extended ideal and its actual tensor coefficient maps.
-/

@[expose] public noncomputable section
open TensorProduct
universe u
namespace FLT.Mazur.FCurve
variable {R B D K : Type u} [CommRing R] [CommRing B] [CommRing D] [Field K]
  [Algebra R B] [Algebra R D] [Algebra B D] [IsScalarTower R B D] [Algebra R K]

/-- Arbitrary localized ambient charts keep Artinian support in every field fiber. -/
theorem artinian_coefficient_quotient_of_localization (M : Submonoid B)
    [IsLocalization M D] (I : Ideal B) [Module.Finite R (B ⧸ I)] :
    IsArtinianRing ((K ⊗[R] D) ⧸
      (I.map (algebraMap B D)).map
        (Algebra.TensorProduct.includeRight (R := R) (A := K))) := by
  let φ := Algebra.TensorProduct.map (AlgHom.id R K) (IsScalarTower.toAlgHom R B D)
  let _ : Algebra (K ⊗[R] B) (K ⊗[R] D) := φ.toAlgebra
  let _ : IsScalarTower K (K ⊗[R] B) (K ⊗[R] D) :=
    .of_algebraMap_eq (by intro k; simp [RingHom.algebraMap_toAlgebra, φ])
  have hφ : (algebraMap (K ⊗[R] B) (K ⊗[R] D)).comp
      (Algebra.TensorProduct.includeRight (R := R) (A := K)).toRingHom =
        (Algebra.TensorProduct.includeRight (R := R) (A := K)).toRingHom.comp
          (algebraMap B D) := by
    ext b
    change φ (1 ⊗ₜ[R] b) = 1 ⊗ₜ[R] (algebraMap B D b)
    simp [φ]
  let _ : IsLocalization
      (M.map (Algebra.TensorProduct.includeRight (R := R) (A := K))) (K ⊗[R] D) :=
    IsLocalization.tensorProduct_tensorProduct_right R K M D hφ
  let J := I.map (Algebra.TensorProduct.includeRight (R := R) (A := K))
  let _ : Module.Finite K ((K ⊗[R] B) ⧸ J) := finite_field_fiber_quotient I
  have h := artinian_localized_finite_quotient (K := K) J
    (M.map (Algebra.TensorProduct.includeRight (R := R) (A := K))) (K ⊗[R] D)
  have he : J.map (algebraMap (K ⊗[R] B) (K ⊗[R] D)) =
      (I.map (algebraMap B D)).map
        (Algebra.TensorProduct.includeRight (R := R) (A := K)) := by
    change (I.map (Algebra.TensorProduct.includeRight (R := R) (A := K)).toRingHom).map
      (algebraMap (K ⊗[R] B) (K ⊗[R] D)) = _
    rw [Ideal.map_map, hφ, ← Ideal.map_map]
    rfl
  rwa [he] at h

end FLT.Mazur.FCurve

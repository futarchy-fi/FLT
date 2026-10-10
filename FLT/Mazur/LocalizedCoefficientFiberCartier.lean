/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.StandardSmoothCoefficientFiber
public import FLT.Mazur.FlatQuotientLocalCartier
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Regular equations in the residue fiber of an ambient local ring

The actual coefficient fiber of a local localization is a local localization
of the smooth affine coefficient fiber. Tensor localization and ideal-map
composition identify its full ideal, so the field-fiber equation theorem
supplies exactly the regular generator required by the relative lifting API.
-/

@[expose] public noncomputable section
open TensorProduct IsLocalRing
universe u
namespace FLT.Mazur.FCurve

variable {R B A : Type u} [CommRing R] [IsLocalRing R] [CommRing B] [CommRing A]
  [Algebra R B] [Algebra R A] [Algebra B A] [IsScalarTower R B A]
  [IsLocalRing A] [IsLocalHom (algebraMap R A)] [Module.Flat R A]
  [Algebra.IsStandardSmoothOfRelativeDimension 1 R B]

/-- The actual residue fiber of a local ambient localization has a regular ideal equation. -/
theorem regular_generator_localized_coefficient_fiber (M : Submonoid B)
    [IsLocalization M A] (I : Ideal B) [Module.Finite R (B ⧸ I)] :
    ∃ a : ResidueField R ⊗[R] A, IsRegular a ∧
      (I.map (algebraMap B A)).map
        (Algebra.TensorProduct.includeRight (R := R) (A := ResidueField R)) =
          Ideal.span {a} := by
  let K := ResidueField R
  let D := K ⊗[R] A
  let φ := Algebra.TensorProduct.map (AlgHom.id R K) (IsScalarTower.toAlgHom R B A)
  let _ : Algebra (K ⊗[R] B) D := φ.toAlgebra
  let _ : IsScalarTower K (K ⊗[R] B) D :=
    .of_algebraMap_eq (by intro k; simp [RingHom.algebraMap_toAlgebra, φ, D])
  have hφ : (algebraMap (K ⊗[R] B) D).comp
      (Algebra.TensorProduct.includeRight (R := R) (A := K)).toRingHom =
        (Algebra.TensorProduct.includeRight (R := R) (A := K)).toRingHom.comp
          (algebraMap B A) := by
    ext b
    change φ (1 ⊗ₜ[R] b) = 1 ⊗ₜ[R] (algebraMap B A b)
    simp [φ]
  let _ : IsLocalization
      (M.map (Algebra.TensorProduct.includeRight (R := R) (A := K))) D :=
    IsLocalization.tensorProduct_tensorProduct_right R K M A hφ
  let _ : Module.FaithfullyFlat R A := .of_flat_of_isLocalHom
  let _ : IsLocalRing D := .of_surjective'
    (Algebra.TensorProduct.includeRight (R := R) (A := K)).toRingHom
    (coefficient_quotient_projection_surjective (B := A) (maximalIdeal R))
  obtain ⟨a, ha, hIa⟩ := regular_generator_field_fiber_localization I
    (M.map (Algebra.TensorProduct.includeRight (R := R) (A := K))) D
  refine ⟨a, ha, ?_⟩
  change (I.map (Algebra.TensorProduct.includeRight (R := R) (A := K)).toRingHom).map
    φ.toRingHom = Ideal.span {a} at hIa
  rw [Ideal.map_map] at hIa
  change I.map ((algebraMap (K ⊗[R] B) D).comp
    (Algebra.TensorProduct.includeRight (R := R) (A := K)).toRingHom) = _ at hIa
  rw [hφ, ← Ideal.map_map] at hIa
  exact hIa

end FLT.Mazur.FCurve

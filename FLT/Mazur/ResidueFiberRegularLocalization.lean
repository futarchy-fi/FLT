/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrimeCoefficientLocalization
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Transporting a regular fiber equation to the ambient local fiber

The original affine residue fiber localizes when the ambient ring localizes.
Flatness of this localization preserves regularity. The canonical tensor
comparison then replaces the base by its local ring at the contracted prime.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.ResidueFiberRegularLocalization
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]

/-- A regular equation on the original residue fiber remains regular on the local fiber. -/
theorem regular_localFiber (q : Ideal B) [q.IsPrime] (a : B)
    (ha : IsRegular (1 ⊗ₜ[R] a : (q.under R).ResidueField ⊗[R] B)) :
    let _ := Localization.AtPrime.algebraOfLiesOver (q.under R) q
    IsRegular (1 ⊗ₜ[Localization.AtPrime (q.under R)]
      algebraMap B (Localization.AtPrime q) a :
        (q.under R).ResidueField ⊗[Localization.AtPrime (q.under R)]
          Localization.AtPrime q) := by
  let K := (q.under R).ResidueField
  let A := Localization.AtPrime q
  let D := K ⊗[R] A
  let φ := Algebra.TensorProduct.map (AlgHom.id R K) (IsScalarTower.toAlgHom R B A)
  let _ : Algebra (K ⊗[R] B) D := φ.toAlgebra
  let _ : IsScalarTower K (K ⊗[R] B) D :=
    .of_algebraMap_eq (by
      intro k
      change k ⊗ₜ[R] 1 = φ (k ⊗ₜ[R] 1)
      simp [φ])
  have hφ : (algebraMap (K ⊗[R] B) D).comp
      (Algebra.TensorProduct.includeRight (R := R) (A := K)).toRingHom =
        (Algebra.TensorProduct.includeRight (R := R) (A := K)).toRingHom.comp
          (algebraMap B A) := by
    ext b
    change φ (1 ⊗ₜ[R] b) = 1 ⊗ₜ[R] (algebraMap B A b)
    simp [φ]
  let _ : IsLocalization
      (q.primeCompl.map (Algebra.TensorProduct.includeRight (R := R) (A := K))) D :=
    IsLocalization.tensorProduct_tensorProduct_right R K q.primeCompl A hφ
  let _ : Module.Flat (K ⊗[R] B) D := IsLocalization.flat D
    (q.primeCompl.map (Algebra.TensorProduct.includeRight (R := R) (A := K)))
  have hr : IsRegular (1 ⊗ₜ[R] algebraMap B A a : D) := by
    rw [← isLeftRegular_iff_isRegular]
    have hs := Module.Flat.isSMulRegular_of_isRegular (M := D) ha
    have hφa : φ (1 ⊗ₜ[R] a) = (1 ⊗ₜ[R] algebraMap B A a : D) := by
      simp [φ]
    intro x y hxy
    apply hs
    change φ (1 ⊗ₜ[R] a) * x = φ (1 ⊗ₜ[R] a) * y
    rw [hφa]
    exact hxy
  let _ := Localization.AtPrime.algebraOfLiesOver (q.under R) q
  let e := IsLocalization.algebraTensorEquiv (q.under R).primeCompl
    (Localization.AtPrime (q.under R)) K A
  rw [← isLeftRegular_iff_isRegular]
  intro x y hxy
  apply e.injective
  apply hr.left
  have he : e (1 ⊗ₜ[Localization.AtPrime (q.under R)] algebraMap B A a) =
      (1 ⊗ₜ[R] algebraMap B A a : D) := rfl
  change (1 ⊗ₜ[R] algebraMap B A a : D) * e x =
    (1 ⊗ₜ[R] algebraMap B A a : D) * e y
  rw [← he, ← map_mul, ← map_mul]
  exact congrArg e hxy

end FLT.Mazur.ResidueFiberRegularLocalization

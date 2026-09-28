/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudRankThreeExtension
public import FLT.Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.Localization.NormTrace

/-!
# Discriminant comparison for finite flat models

A model morphism which is an isomorphism on the generic fibre preserves traces.
Its integral discriminants therefore differ by the square of its matrix determinant.
When the discriminants are nonzero and associated, the matrix determinant is a unit,
so the integral morphism is an isomorphism.

This is the algebraic comparison step in the discriminant route to Raynaud rigidity.
It does not prove that generically isomorphic three-primary models have the same
discriminant ideal. Order alone does not determine that ideal: the constant group of
order three has unit discriminant, whereas the coordinate algebra of `μ₃` has
power-basis discriminant `-27`. Their generic fibres are different.

The alternative multiplication-by-three filtration uses finite-flat subobjects and
quotients already constructed in `FiniteFlatSubobject` and `FiniteFlat`; it still
needs rigidity for arbitrary rank killed-by-three models, not only rank three.
-/

@[expose] public noncomputable section

open scoped TensorProduct nonZeroDivisors

universe u v
namespace ThreeAdicPlan

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

omit [IsDomain R] [IsFractionRing R K] in
/-- A finite free model with étale generic fibre has nonzero discriminant in every basis. -/
theorem FF.discr_ne_zero (X : FF R K) {ι : Type v} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R X.CoordinateRing) : Algebra.discr R b ≠ 0 := by
  have hne := Algebra.discr_ne_zero_of_etale (b.baseChange K)
  rw [Algebra.discr_baseChange] at hne
  exact fun h ↦ hne (by rw [h, map_zero])

omit [IsDomain R] in
/-- A generically invertible morphism of finite free models preserves integral traces. -/
theorem ModelHom.trace_eq_of_baseChange_bijective {X Y : FF R K}
    [Module.Free R X.CoordinateRing] [Module.Free R Y.CoordinateRing]
    (f : ModelHom X Y) (hf : Function.Bijective f.baseChange) (y : Y.CoordinateRing) :
    Algebra.trace R X.CoordinateRing (f y) = Algebra.trace R Y.CoordinateRing y := by
  let : Algebra X.CoordinateRing (K ⊗[R] X.CoordinateRing) :=
    Algebra.TensorProduct.rightAlgebra
  let : Algebra Y.CoordinateRing (K ⊗[R] Y.CoordinateRing) :=
    Algebra.TensorProduct.rightAlgebra
  apply IsFractionRing.injective R K
  rw [← Algebra.trace_localization R R⁰ (Rₘ := K) (Sₘ := K ⊗[R] X.CoordinateRing),
    ← Algebra.trace_localization R R⁰ (Rₘ := K) (Sₘ := K ⊗[R] Y.CoordinateRing)]
  exact Algebra.trace_eq_of_algEquiv (AlgEquiv.ofBijective f.baseChange.toAlgHom hf)
    (1 ⊗ₜ[R] y)

omit [IsDomain R] in
/-- A generically invertible model morphism preserves the discriminant of a family. -/
theorem ModelHom.discr_map_of_baseChange_bijective {X Y : FF R K}
    [Module.Free R X.CoordinateRing] [Module.Free R Y.CoordinateRing]
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (f : ModelHom X Y) (hf : Function.Bijective f.baseChange)
    (b : ι → Y.CoordinateRing) : Algebra.discr R (f ∘ b) = Algebra.discr R b := by
  classical
  unfold Algebra.discr
  congr 1
  ext i j
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Function.comp_apply,
    ← map_mul, f.trace_eq_of_baseChange_bijective hf]

omit [IsDomain R] in
/-- The index formula: a generic isomorphism changes discriminants by a determinant square. -/
theorem ModelHom.discr_eq_det_sq_mul {X Y : FF R K}
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (f : ModelHom X Y) (hf : Function.Bijective f.baseChange)
    (bY : Module.Basis ι R Y.CoordinateRing) (bX : Module.Basis ι R X.CoordinateRing) :
    Algebra.discr R bY =
      (LinearMap.toMatrix bY bX f.toLinearMap).det ^ 2 * Algebra.discr R bX := by
  let : Module.Free R X.CoordinateRing := Module.Free.of_basis bX
  let : Module.Free R Y.CoordinateRing := Module.Free.of_basis bY
  rw [← f.discr_map_of_baseChange_bijective hf bY]
  convert Algebra.discr_of_matrix_vecMul bX (bX.toMatrix (f ∘ bY)) using 1
  · rw [Module.Basis.toMatrix_map_vecMul]
  · congr 3
    ext i j
    simp [LinearMap.toMatrix_apply, Module.Basis.toMatrix_apply, BialgHom.toCoalgHom_apply]

/-- Associated nonzero discriminants force an integral model morphism to be bijective.
The discriminant association is a separate arithmetic obligation. -/
theorem ModelHom.bijective_of_discr_associated {X Y : FF R K}
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (f : ModelHom X Y) (hf : Function.Bijective f.baseChange)
    (bY : Module.Basis ι R Y.CoordinateRing) (bX : Module.Basis ι R X.CoordinateRing)
    (hdisc : Associated (Algebra.discr R bY) (Algebra.discr R bX)) :
    Function.Bijective f := by
  have hne := X.discr_ne_zero bX
  have he := f.discr_eq_det_sq_mul hf bY bX
  rw [he] at hdisc
  have hu : IsUnit ((LinearMap.toMatrix bY bX f.toLinearMap).det ^ 2) := by
    have ha : Associated ((LinearMap.toMatrix bY bX f.toLinearMap).det ^ 2) 1 :=
      Associated.of_mul_right (by simpa only [one_mul] using hdisc) (Associated.refl _) hne
    exact ha.isUnit_iff.mpr isUnit_one
  exact (LinearEquiv.ofIsUnitDet ((isUnit_pow_iff (by decide : 2 ≠ 0)).mp hu)).bijective

/-- Association of the source and graph discriminants makes the first graph projection
surjective. This isolates the discriminant equality still needed for general Raynaud rigidity. -/
theorem GenericGaloisHom.graphFst_surjective_of_discr_associated
    {X Y : FF ℤ_[3] ℚ_[3]} (f : GenericGaloisHom X Y)
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (bX : Module.Basis ι ℤ_[3] X.CoordinateRing)
    (bG : Module.Basis ι ℤ_[3] f.graphClosure.CoordinateRing)
    (hdisc : Associated (Algebra.discr ℤ_[3] bX) (Algebra.discr ℤ_[3] bG)) :
    Function.Surjective f.graphFst :=
  (f.graphFst.bijective_of_discr_associated f.graphFst_baseChange_bijective bX bG hdisc).2

end ThreeAdicPlan

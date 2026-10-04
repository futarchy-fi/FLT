/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleDivisionCover
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.FiniteStability

/-! # Finiteness and finite presentation of the actual division cover

Finite presentation alone does not prove that arbitrary lifted relations remain flat.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace AlgHom
variable {R A H C : Type} [CommRing R] [CommRing A] [CommRing H] [CommRing C]
  [Algebra R A] [Algebra R H] [Algebra R C]
  [Module.Finite R A] [Module.Finite R H] [Module.FinitePresentation R H]

/-- The actual pullback point cover is finite and finitely presented as well as faithfully flat. -/
theorem exists_finitePresentation_point_cover (f : A →ₐ[R] H)
    (hf : f.toRingHom.FaithfullyFlat) (x : A →ₐ[R] C) :
    ∃ (D : Type) (_ : CommRing D) (_ : Algebra R D) (_ : Algebra C D)
      (_ : IsScalarTower R C D),
      Module.Finite C D ∧ Algebra.FinitePresentation C D ∧ Module.FaithfullyFlat C D ∧
        ∃ y : H →ₐ[R] D, y.comp f = (IsScalarTower.toAlgHom R C D).comp x := by
  let : Algebra A H := f.toRingHom.toAlgebra
  let : Algebra A C := x.toRingHom.toAlgebra
  let : IsScalarTower R A H := IsScalarTower.of_algHom f
  let : IsScalarTower R A C := IsScalarTower.of_algHom x
  let : Module.FaithfullyFlat A H := hf
  let : Module.Finite A H := Module.Finite.of_restrictScalars_finite R A H
  let : Algebra.FinitePresentation A H :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R A H
  let D := C ⊗[A] H
  let y : H →ₐ[R] D := (Algebra.TensorProduct.includeRight : H →ₐ[A] D).restrictScalars R
  refine ⟨D, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, y, ?_⟩
  ext a
  change (1 : C) ⊗ₜ[A] f a = x a ⊗ₜ[A] (1 : H)
  exact (Algebra.TensorProduct.tmul_one_eq_one_tmul a).symm

end AlgHom
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K C : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] [CommRing C] [Algebra R C]
  {p height : ℕ} [Fact p.Prime] (X : PDivisibleSystem R K p height)

/-- The specified original reduction admits a finite, finitely presented actual point cover. -/
theorem exists_finitePresentation_reduction_cover {n m : ℕ} (h : n ≤ m)
    (x : (X.level n).CoordinateRing →ₐ[R] C) :
    ∃ (D : Type) (_ : CommRing D) (_ : Algebra R D) (_ : Algebra C D)
      (_ : IsScalarTower R C D),
      Module.Finite C D ∧ Algebra.FinitePresentation C D ∧ Module.FaithfullyFlat C D ∧
        ∃ y : (X.level m).CoordinateRing →ₐ[R] D,
          y.comp (X.reduction h).toAlgHom = (IsScalarTower.toAlgHom R C D).comp x := by
  let : Module.Free R (X.level m).CoordinateRing := Module.free_of_flat_of_isLocalRing
  let : Module.FinitePresentation R (X.level m).CoordinateRing :=
    Module.finitePresentation_of_projective _ _
  exact AlgHom.exists_finitePresentation_point_cover _ (X.faithfullyFlat h) x

end ThreeAdicPlan.PDivisibleSystem

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.DivisionGeometricFibre
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct

/-! # Geometric comparison of the original residue-field division fibre -/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan.PDivisibleSystem

variable {R K k Ω : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] [Field k] [Algebra R k]
  [Field Ω] [IsAlgClosed Ω] [Algebra k Ω] [Algebra R Ω] [IsScalarTower R k Ω]
  {p height : ℕ} [Fact p.Prime] (X : PDivisibleSystem R K p height) (m n : ℕ)

/-- The geometric extension of the actual residue fibre is the base change of the
original kernel level. The residue point need not be rational over the original base. -/
theorem nonempty_residue_division_fibre_comparison
    (x : (X.level n).CoordinateRing →ₐ[R] k) :
    let : Algebra (X.level n).CoordinateRing (X.level (m + n)).CoordinateRing :=
      (X.reduction (Nat.le_add_left n m)).toAlgHom.toRingHom.toAlgebra
    let : Algebra (X.level n).CoordinateRing k := x.toRingHom.toAlgebra
    Nonempty ((Ω ⊗[k] (k ⊗[(X.level n).CoordinateRing]
      (X.level (m + n)).CoordinateRing)) ≃ₐ[Ω] Ω ⊗[R] (X.level m).CoordinateRing) := by
  let f := (X.reduction (Nat.le_add_left n m)).toAlgHom
  let : Algebra (X.level n).CoordinateRing (X.level (m + n)).CoordinateRing :=
    f.toRingHom.toAlgebra
  let : Algebra (X.level n).CoordinateRing k := x.toRingHom.toAlgebra
  let : IsScalarTower R (X.level n).CoordinateRing k := IsScalarTower.of_algHom x
  let xΩ := (IsScalarTower.toAlgHom R k Ω).comp x
  let : Algebra (X.level n).CoordinateRing Ω := xΩ.toRingHom.toAlgebra
  let : IsScalarTower (X.level n).CoordinateRing k Ω :=
    IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨_, _, e, _⟩ := X.exists_geometric_division_fibre_equiv (Ω := Ω) m n xΩ
  exact ⟨(Algebra.TensorProduct.cancelBaseChange (X.level n).CoordinateRing k Ω Ω
    (X.level (m + n)).CoordinateRing).trans e⟩

end ThreeAdicPlan.PDivisibleSystem

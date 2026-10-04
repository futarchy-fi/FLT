/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleKernelFibre
public import FLT.GroupScheme.GeometricFibrePoint

/-! # The actual geometric division fibre and its original kernel

The fibre is taken at the specified geometric point. A lift exists by
finite faithful flatness, and translation retains the original inclusion
in the coordinate formula. No complete-intersection assertion is made.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K Ω : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
  {p height : ℕ} [Fact p.Prime] (X : PDivisibleSystem R K p height)

/-- A specified geometric division fibre is isomorphic to the original kernel,
with the original comultiplication and inclusion as its coordinate map. -/
theorem exists_geometric_division_fibre_equiv (m n : ℕ)
    (x : (X.level n).CoordinateRing →ₐ[R] Ω) :
    let : Algebra (X.level n).CoordinateRing (X.level (m + n)).CoordinateRing :=
      (X.reduction (Nat.le_add_left n m)).toAlgHom.toRingHom.toAlgebra
    let : Algebra (X.level n).CoordinateRing Ω := x.toRingHom.toAlgebra
    ∃ (y : (X.level (m + n)).CoordinateRing →ₐ[R] Ω),
      y.comp (X.reduction (Nat.le_add_left n m)).toAlgHom = x ∧
      ∃ e : Ω ⊗[(X.level n).CoordinateRing] (X.level (m + n)).CoordinateRing ≃ₐ[Ω]
          Ω ⊗[R] (X.level m).CoordinateRing,
        ∀ a, e (1 ⊗ₜ[(X.level n).CoordinateRing] a) =
          Algebra.TensorProduct.map y (X.inclusion (Nat.le_add_right m n)).toAlgHom
            (Coalgebra.comul a) := by
  let f := (X.reduction (Nat.le_add_left n m)).toAlgHom
  let : Algebra (X.level n).CoordinateRing (X.level (m + n)).CoordinateRing :=
    f.toRingHom.toAlgebra
  let : Algebra (X.level n).CoordinateRing Ω := x.toRingHom.toAlgebra
  let : IsScalarTower R (X.level n).CoordinateRing (X.level (m + n)).CoordinateRing :=
    IsScalarTower.of_algHom f
  let : Module.Finite (X.level n).CoordinateRing (X.level (m + n)).CoordinateRing :=
    Module.Finite.of_restrictScalars_finite R _ _
  obtain ⟨y, hy⟩ := f.exists_lift_of_finite_faithfullyFlat
    (X.faithfullyFlat (Nat.le_add_left n m)) (inferInstance : Module.Finite _ _) x
  let : Algebra (X.level (m + n)).CoordinateRing Ω := y.toRingHom.toAlgebra
  let : IsScalarTower R (X.level (m + n)).CoordinateRing Ω := IsScalarTower.of_algHom y
  let : IsScalarTower (X.level n).CoordinateRing (X.level (m + n)).CoordinateRing Ω :=
    IsScalarTower.of_algebraMap_eq' (congrArg AlgHom.toRingHom hy.symm)
  refine ⟨y, hy, X.pointedDivisionFibreEquiv m n rfl, ?_⟩
  intro a
  exact X.pointedDivisionFibreEquiv_one_tmul m n rfl a

end ThreeAdicPlan.PDivisibleSystem

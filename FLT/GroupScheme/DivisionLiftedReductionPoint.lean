/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.DivisionLiftedFlatCharts
public import FLT.GroupScheme.FiniteProductReductionPoint
public import FLT.GroupScheme.LiftedPresentationPoint
public import FLT.GroupScheme.PrincipalDivisionPoint

/-! # The original division point on the reduction of a faithfully flat lifted cover -/

@[expose] public noncomputable section
open scoped TensorProduct
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K B C : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C] [Algebra B C] [IsScalarTower R B C]
  {p height : ℕ} [Fact p.Prime] (X : PDivisibleSystem R K p height)

/-- The W50 charts carry the original division point on their actual tensor reduction.
The cover and its faithful flatness are constructed, not supplied by the caller. -/
theorem exists_division_point_on_lifted_cover
    (hq : Function.Surjective (algebraMap B C)) {k : ℕ}
    (hn : RingHom.ker (algebraMap B C) ^ k = ⊥)
    (hC : IsNilpotent (p : C)) (m n : ℕ) (x : (X.level n).CoordinateRing →ₐ[R] C) :
    ∃ (D : Type) (_ : CommRing D) (_ : Algebra B D) (_ : Algebra R D)
      (_ : IsScalarTower R B D), Module.FaithfullyFlat B D ∧
      ∃ z : (X.level (m + n)).CoordinateRing →ₐ[R] D ⊗[B] C,
        z.comp (X.reduction (Nat.le_add_left n m)).toAlgHom =
          (Algebra.TensorProduct.includeRight.restrictScalars R).comp x := by
  classical
  let : Algebra (X.level n).CoordinateRing (X.level (m + n)).CoordinateRing :=
    (X.reduction (Nat.le_add_left n m)).toAlgHom.toRingHom.toAlgebra
  let : Algebra (X.level n).CoordinateRing C := x.toRingHom.toAlgebra
  let : IsScalarTower R (X.level n).CoordinateRing (X.level (m + n)).CoordinateRing :=
    IsScalarTower.of_algHom (X.reduction (Nat.le_add_left n m)).toAlgHom
  let : IsScalarTower R (X.level n).CoordinateRing C := IsScalarTower.of_algHom x
  let A := C ⊗[(X.level n).CoordinateRing] (X.level (m + n)).CoordinateRing
  obtain ⟨d, f, _, t, a, P, g, hg, _, hflat, _⟩ :=
    X.exists_division_lifted_flat_charts m n hq hn hC x
  let D i := MvPolynomial (Fin (d + 1)) B ⧸ Ideal.span (Set.range (g i))
  have hz (i : t) : ∃ z : (X.level (m + n)).CoordinateRing →ₐ[R] D i ⊗[B] C,
      z.comp (X.reduction (Nat.le_add_left n m)).toAlgHom =
        (Algebra.TensorProduct.includeRight.restrictScalars R).comp x := by
    let E := Localization.Away (f (a i))
    let y : (X.level (m + n)).CoordinateRing →ₐ[R] E :=
      (IsScalarTower.toAlgHom R A E).comp
        (Algebra.TensorProduct.includeRight.restrictScalars R)
    obtain ⟨z, _, hz⟩ := (P i).exists_point_on_lifted_reduction_over_base (g i) (hg i) hq
      (X.reduction (Nat.le_add_left n m)).toAlgHom x y
      (AlgHom.principal_pullback_point_comp (R := R) (f (a i)))
    exact ⟨z, hz⟩
  choose z hz using hz
  exact ⟨∀ i, D i, inferInstance, inferInstance, inferInstance, inferInstance, hflat,
    AlgHom.exists_finiteProduct_reduction_point D _ x z hz⟩

end ThreeAdicPlan.PDivisibleSystem

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicTorsionGenericPoints
public import FLT.EllipticCurve.Torsion
public import FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
/-! # Constructed finite-flat torsion at good reduction away from its order -/

open scoped WeierstrassCurve.Affine TensorProduct
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
universe u
variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]
  [IsNoetherianRing R] [IsDomain R]
  (W : WeierstrassCurve R) [W.IsElliptic]
  (E : WeierstrassCurve K) [E.IsElliptic]
  [DecidableEq K] [DecidableEq (AlgebraicClosure K)]
/-- An integral model identifies its geometric point group with that of the generic curve. -/
def modelGeometricPointEquiv (h : W.map (algebraMap R K) = E) :
    (W.map (algebraMap R (AlgebraicClosure K))).toAffine.Point ≃+
      ((E.map (algebraMap K (AlgebraicClosure K)))⁄(AlgebraicClosure K)).Point :=
  Affine.Point.equivOfEq (by
    change W.map (algebraMap R (AlgebraicClosure K)) =
      (E.map (algebraMap K (AlgebraicClosure K))).map
        (algebraMap (AlgebraicClosure K) (AlgebraicClosure K))
    rw [Algebra.algebraMap_self, WeierstrassCurve.map_id, ← h,
      WeierstrassCurve.map_map, ← IsScalarTower.algebraMap_eq])

/-- The model point comparison restricts to the torsion representation carrier. -/
def modelGeometricTorsionEquiv (h : W.map (algebraMap R K) = E) (n : ℕ) :
    (nsmulAddMonoidHom n :
      (W.map (algebraMap R (AlgebraicClosure K))).toAffine.Point →+
      (W.map (algebraMap R (AlgebraicClosure K))).toAffine.Point).ker ≃+
      (E.map (algebraMap K (AlgebraicClosure K))).nTorsion n where
  toFun P := ⟨modelGeometricPointEquiv W E h P.val, by
    change (n : ℤ) • modelGeometricPointEquiv W E h P.val = 0
    rw [natCast_zsmul, ← map_nsmul, show n • P.val = 0 from P.property, map_zero]⟩
  invFun P := ⟨(modelGeometricPointEquiv W E h).symm P.val, by
    change n • (modelGeometricPointEquiv W E h).symm P.val = 0
    rw [← map_nsmul]
    have hp : n • P.val = 0 := by
      simpa only [Submodule.mem_torsionBy_iff, natCast_zsmul] using P.property
    rw [hp, map_zero]⟩
  left_inv P := Subtype.ext ((modelGeometricPointEquiv W E h).symm_apply_apply _)
  right_inv P := Subtype.ext ((modelGeometricPointEquiv W E h).apply_symm_apply _)
  map_add' P Q := Subtype.ext (map_add _ _ _)

omit [IsNoetherianRing R] [IsDomain R] [W.IsElliptic] in
/-- The model torsion comparison intertwines the actual Galois representation. -/
theorem modelGeometricTorsionEquiv_map (h : W.map (algebraMap R K) = E)
    (n : ℕ) (hn : 0 < n) (σ : Field.absoluteGaloisGroup K)
    (P : (nsmulAddMonoidHom n :
      (W.map (algebraMap R (AlgebraicClosure K))).toAffine.Point →+
      (W.map (algebraMap R (AlgebraicClosure K))).toAffine.Point).ker) :
    modelGeometricTorsionEquiv W E h n
      (classicalTorsionMap W n (σ.toAlgHom.restrictScalars R) P) =
        E.galoisRep n hn σ (modelGeometricTorsionEquiv W E h n P) := by
  apply Subtype.ext
  change modelGeometricPointEquiv W E h (Affine.Point.map
      (σ.toAlgHom.restrictScalars R) P.val) =
    Affine.Point.map (W' := E.toAffine) σ.toAlgHom (modelGeometricPointEquiv W E h P.val)
  cases P.val with
  | zero => simp only [← Affine.Point.zero_def, map_zero]
  | some x y hp =>
    simp only [modelGeometricPointEquiv, Affine.Point.map_some, Affine.Point.equivOfEq_some]
    rfl

/-- An elliptic integral model gives finite-flat torsion of invertible order. -/
theorem isFiniteFlat_torsion_of_integral_model (h : W.map (algebraMap R K) = E)
    (n : ℕ) (hn : 0 < n) (hu : IsUnit (n : R)) :
    GaloisModule.IsFiniteFlat R K (AlgebraicClosure K) (E.galoisRep n hn).Space := by
  have : NeZero n := ⟨Nat.ne_of_gt hn⟩
  exact isFiniteFlat_of_unit_torsion W n hu (modelGeometricTorsionEquiv W E h n)
    (modelGeometricTorsionEquiv_map W E h n hn)
end WeierstrassCurve.CubicCharts

namespace WeierstrassCurve.CubicCharts
universe u
variable (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [DecidableEq K] [DecidableEq (AlgebraicClosure K)]
    (E : WeierstrassCurve K) [E.IsElliptic] [E.HasGoodReduction R]
/-- Good reduction gives finite-flat torsion when the order is a unit in the valuation ring. -/
theorem isFiniteFlat_torsion_of_goodReduction_unit
    (n : ℕ) (hn : 0 < n) (hu : IsUnit (n : R)) :
    GaloisModule.IsFiniteFlat R K (AlgebraicClosure K) (E.galoisRep n hn).Space := by
  let W := integralModel R E
  have hred : (E.reduction R).IsElliptic :=
    (hasGoodReduction_iff_isElliptic_reduction R).mp inferInstance
  have hΔ : IsUnit W.Δ := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    have hd := (E.reduction R).isUnit_Δ
    simpa only [reduction, map_Δ, isUnit_iff_ne_zero] using hd
  have : W.IsElliptic := ⟨hΔ⟩
  exact isFiniteFlat_torsion_of_integral_model W E
    (baseChange_integralModel_eq R E) n hn hu
end WeierstrassCurve.CubicCharts

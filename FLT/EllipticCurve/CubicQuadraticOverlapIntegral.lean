/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicQuadraticOverlap

/-! # Integral presentations of quadratic overlap charts

When two is invertible, each of the two sign charts in the kernel pair
of a quadratic étale cover is a copy of the cover itself. Evaluation
on the tensor product, with the appropriate root sign, gives an explicit
inverse to the second projection on each localized chart.
Thus these charts inherit domain and noetherian properties of the cover;
the entire tensor product need not be a domain.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts
variable {R : Type*} [CommRing R]
/-- The identity or sign involution specified by a sign chart. -/
def quadraticSignEnd (d : Rˣ) : Bool → (QuadraticEtaleRing d →ₐ[R] QuadraticEtaleRing d)
  | false => quadraticEtaleNeg d
  | true => AlgHom.id R _
/-- Tensor-product evaluation with the prescribed relative root sign. -/
def quadraticOverlapEval (d : Rˣ) (i : Bool) :
    QuadraticOverlapRing d →ₐ[R] QuadraticEtaleRing d :=
  Algebra.TensorProduct.lift (quadraticSignEnd d i) (AlgHom.id R _)
    (fun _ _ => Commute.all _ _)
/-- Evaluation on the first factor applies the chosen sign. -/
theorem quadraticOverlapEval_left (d : Rˣ) (i : Bool) :
    (quadraticOverlapEval d i).comp Algebra.TensorProduct.includeLeft = quadraticSignEnd d i :=
  Algebra.TensorProduct.lift_comp_includeLeft _ _ _
/-- Evaluation on the second factor is the identity. -/
theorem quadraticOverlapEval_right (d : Rˣ) (i : Bool) :
    (quadraticOverlapEval d i).comp Algebra.TensorProduct.includeRight = AlgHom.id R _ :=
  Algebra.TensorProduct.lift_comp_includeRight' _ _ _
/-- The chart denominator evaluates to a unit when two is invertible. -/
theorem quadraticOverlapEval_unit (d : Rˣ) (h2 : IsUnit (2 : R)) (i : Bool) :
    IsUnit (quadraticOverlapEval d i (quadraticSignDenominator
      (quadraticOverlapLeftRoot d : QuadraticOverlapRing d)
      (quadraticOverlapRightRoot d : QuadraticOverlapRing d) i)) := by
  have ht : IsUnit (2 : QuadraticEtaleRing d) := by
    simpa only [map_ofNat] using h2.map (algebraMap R (QuadraticEtaleRing d))
  have hu : IsUnit (2 * (quadraticEtaleUnit d : QuadraticEtaleRing d)) :=
    ht.mul (quadraticEtaleUnit d).isUnit
  have hl : quadraticOverlapEval d i
      (quadraticOverlapLeftRoot d : QuadraticOverlapRing d) =
        quadraticSignEnd d i (quadraticEtaleUnit d : QuadraticEtaleRing d) :=
    DFunLike.congr_fun (quadraticOverlapEval_left d i) _
  have hr : quadraticOverlapEval d i
      (quadraticOverlapRightRoot d : QuadraticOverlapRing d) =
        (quadraticEtaleUnit d : QuadraticEtaleRing d) :=
    DFunLike.congr_fun (quadraticOverlapEval_right d i) _
  cases i
  · change IsUnit (quadraticOverlapEval d false
      ((quadraticOverlapLeftRoot d : QuadraticOverlapRing d) -
        (quadraticOverlapRightRoot d : QuadraticOverlapRing d)))
    rw [map_sub, hl, hr]
    change IsUnit (quadraticEtaleNeg d (quadraticEtaleUnit d : QuadraticEtaleRing d) - _)
    rw [quadraticEtaleNeg_unit]
    convert hu.neg using 1
    ring
  · change IsUnit (quadraticOverlapEval d true
      ((quadraticOverlapLeftRoot d : QuadraticOverlapRing d) +
        (quadraticOverlapRightRoot d : QuadraticOverlapRing d)))
    rw [map_add, hl, hr]
    change IsUnit ((quadraticEtaleUnit d : QuadraticEtaleRing d) + _)
    simpa only [two_mul] using hu
/-- Evaluation extended to the localized sign chart. -/
def quadraticOverlapChartEval (d : Rˣ) (h2 : IsUnit (2 : R)) (i : Bool) :
    QuadraticOverlapChartRing d i →ₐ[R] QuadraticEtaleRing d :=
  IsLocalization.Away.liftAlgHom _ (quadraticOverlapEval_unit d h2 i)
/-- Localized evaluation agrees with tensor-product evaluation. -/
theorem quadraticOverlapChartEval_base (d : Rˣ) (h2 : IsUnit (2 : R)) (i : Bool)
    (x : QuadraticOverlapRing d) :
    quadraticOverlapChartEval d h2 i
      (algebraMap (QuadraticOverlapRing d) (QuadraticOverlapChartRing d i) x) =
        quadraticOverlapEval d i x :=
  IsLocalization.Away.lift_eq _ (quadraticOverlapEval_unit d h2 i) _
/-- Evaluation is a left inverse to the second chart projection. -/
theorem quadraticOverlapChartEval_right (d : Rˣ) (h2 : IsUnit (2 : R)) (i : Bool) :
    (quadraticOverlapChartEval d h2 i).comp (quadraticOverlapRightMap d i) =
      AlgHom.id R (QuadraticEtaleRing d) := by
  apply AlgHom.ext
  intro x
  change quadraticOverlapChartEval d h2 i
    (algebraMap (QuadraticOverlapRing d) (QuadraticOverlapChartRing d i)
      (Algebra.TensorProduct.includeRight x)) = x
  rw [quadraticOverlapChartEval_base]
  exact DFunLike.congr_fun (quadraticOverlapEval_right d i) x
/-- The first projection is the signed second projection. -/
theorem quadraticOverlapRightMap_sign (d : Rˣ) (i : Bool) :
    (quadraticOverlapRightMap d i).comp (quadraticSignEnd d i) =
      quadraticOverlapLeftMap d i := by
  cases i
  · exact (quadraticOverlapMaps_opposite d).symm
  · exact (quadraticOverlapMaps_equal d).symm
/-- Evaluation is also a right inverse to the second chart projection. -/
theorem quadraticOverlapChartEval_inverse (d : Rˣ) (h2 : IsUnit (2 : R)) (i : Bool) :
    (quadraticOverlapRightMap d i).comp (quadraticOverlapChartEval d h2 i) =
      AlgHom.id R (QuadraticOverlapChartRing d i) := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (quadraticSignDenominator
    (quadraticOverlapLeftRoot d : QuadraticOverlapRing d)
    (quadraticOverlapRightRoot d : QuadraticOverlapRing d) i))
  change ((quadraticOverlapRightMap d i).toRingHom.comp
    ((quadraticOverlapChartEval d h2 i).toRingHom.comp
      (algebraMap (QuadraticOverlapRing d) (QuadraticOverlapChartRing d i)))) = _
  rw [quadraticOverlapChartEval, IsLocalization.Away.liftAlgHom_toRingHom,
    IsLocalization.Away.lift_comp]
  have h : (quadraticOverlapRightMap d i).comp (quadraticOverlapEval d i) =
      IsScalarTower.toAlgHom R (QuadraticOverlapRing d) (QuadraticOverlapChartRing d i) := by
    apply Algebra.TensorProduct.ext
    · rw [AlgHom.comp_assoc, quadraticOverlapEval_left, quadraticOverlapRightMap_sign]
      rfl
    · change ((quadraticOverlapRightMap d i).comp (quadraticOverlapEval d i)).comp
        Algebra.TensorProduct.includeRight = _
      rw [AlgHom.comp_assoc, quadraticOverlapEval_right, AlgHom.comp_id]
      rfl
  exact congrArg AlgHom.toRingHom h
/-- Each sign chart is explicitly isomorphic to the quadratic cover algebra. -/
def quadraticOverlapChartEquiv (d : Rˣ) (h2 : IsUnit (2 : R)) (i : Bool) :
    QuadraticOverlapChartRing d i ≃ₐ[R] QuadraticEtaleRing d :=
  AlgEquiv.ofAlgHom (quadraticOverlapChartEval d h2 i) (quadraticOverlapRightMap d i)
    (quadraticOverlapChartEval_right d h2 i) (quadraticOverlapChartEval_inverse d h2 i)

instance quadraticOverlapChartDomain (d : Rˣ) [Fact (IsUnit (2 : R))]
    [IsDomain (QuadraticEtaleRing d)] (i : Bool) :
    IsDomain (QuadraticOverlapChartRing d i) :=
  (quadraticOverlapChartEquiv d Fact.out i).toMulEquiv.isDomain (QuadraticEtaleRing d)
instance quadraticOverlapChartNoetherian (d : Rˣ) [Fact (IsUnit (2 : R))]
    [IsNoetherianRing (QuadraticEtaleRing d)] (i : Bool) :
    IsNoetherianRing (QuadraticOverlapChartRing d i) :=
  isNoetherianRing_of_ringEquiv (QuadraticEtaleRing d)
    (quadraticOverlapChartEquiv d Fact.out i).symm.toRingEquiv
instance quadraticOverlapChartLevelUnit (d : Rˣ) (p : ℕ)
    [Fact (IsUnit (p : QuadraticEtaleRing d))] (i : Bool) :
    Fact (IsUnit (p : QuadraticOverlapChartRing d i)) := by
  constructor
  simpa only [map_natCast] using
    (Fact.out : IsUnit (p : QuadraticEtaleRing d)).map (quadraticOverlapRightMap d i)
end WeierstrassCurve.CubicCharts

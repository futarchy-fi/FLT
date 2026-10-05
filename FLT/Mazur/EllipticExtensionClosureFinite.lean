/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticExtensionClosureQuasiFinite
public import FLT.Mazur.EllipticSubgroupClosureFinite

/-!
# Finite flat closure of the transported prime-order subgroup

The proved cardinality of the transported subgroup makes its actual Y/Z closure
finite. Over a DVR its already proved flatness gives a finite flat scheme.
No integral group law or rank computation is asserted here.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace FLT.Mazur

open WeierstrassCurve

variable {R K L : Type*} [CommRing R] [Field K] [Field L]
  [Algebra R K] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
  [DecidableEq K] [DecidableEq L]
  (A : ValuationSubring L) (W : WeierstrassCurve R) (U : WeierstrassCurve A)
  [(W.map (algebraMap R L)).IsElliptic] (C : VariableChange L)
  (hC : C • W.map (algebraMap R L) = U.map (algebraMap A L))
  (P : (W.map (algebraMap R K)).toAffine.Point)

/-- The actual transported prime subgroup closure is finite over the valuation ring. -/
theorem ellipticExtensionClosure_isFinite {p : ℕ} [Fact p.Prime]
    (hP : p • P = 0) (hP0 : P ≠ 0) :
    IsFinite (EllipticSubgroupChart.closureToBase A U
      (ellipticExtensionProjectiveSubgroup A W U C hC P) 1 2) := by
  let _ := Nat.finite_of_card_ne_zero
    ((ellipticExtensionProjectiveSubgroup_card A W U C hC P hP hP0).trans_ne
      (Fact.out : p.Prime).ne_zero)
  infer_instance

/-- Over a DVR the concrete closure is a finite flat scheme over the base. -/
theorem ellipticExtensionClosure_finite_flat [IsDedekindDomain A] {p : ℕ} [Fact p.Prime]
    (hP : p • P = 0) (hP0 : P ≠ 0) :
    IsFinite (EllipticSubgroupChart.closureToBase A U
      (ellipticExtensionProjectiveSubgroup A W U C hC P) 1 2) ∧
    Flat (EllipticSubgroupChart.closureToBase A U
      (ellipticExtensionProjectiveSubgroup A W U C hC P) 1 2) :=
  ⟨ellipticExtensionClosure_isFinite A W U C hC P hP hP0, inferInstance⟩

end FLT.Mazur

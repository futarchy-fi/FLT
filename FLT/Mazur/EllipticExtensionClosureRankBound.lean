/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticExtensionClosureFinite
public import FLT.Mazur.EllipticSubgroupGlobalRankBound

/-!
# Rank bound for the transported prime subgroup closure

The global evaluation injection and the proved subgroup cardinality give an
upper bound p for the integral rank. Equality remains the next obligation.
-/

@[expose] public noncomputable section

namespace FLT.Mazur

open WeierstrassCurve

variable {R K L : Type*} [CommRing R] [Field K] [Field L]
  [Algebra R K] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
  [DecidableEq K] [DecidableEq L]
  (A : ValuationSubring L) (W : WeierstrassCurve R) (U : WeierstrassCurve A)
  [(W.map (algebraMap R L)).IsElliptic] (C : VariableChange L)
  (hC : C • W.map (algebraMap R L) = U.map (algebraMap A L))
  (P : (W.map (algebraMap R K)).toAffine.Point)

/-- The actual prime subgroup closure's integral coordinate rank is at most p. -/
theorem ellipticExtensionClosure_finrank_le {p : ℕ} [Fact p.Prime]
    (hP : p • P = 0) (hP0 : P ≠ 0) :
    Module.finrank A (EllipticSubgroupChart.GlobalClosure A U
      (ellipticExtensionProjectiveSubgroup A W U C hC P)) ≤ p := by
  let _ := Nat.finite_of_card_ne_zero
    ((ellipticExtensionProjectiveSubgroup_card A W U C hC P hP hP0).trans_ne
      (Fact.out : p.Prime).ne_zero)
  exact (EllipticSubgroupChart.globalClosure_finrank_le_card A U
    (ellipticExtensionProjectiveSubgroup A W U C hC P)).trans_eq
      (ellipticExtensionProjectiveSubgroup_card A W U C hC P hP hP0)

end FLT.Mazur

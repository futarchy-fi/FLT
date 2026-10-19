/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProperFlatValuationFinite
public import FLT.Mazur.WeierstrassGenericKernelRecovery
public import FLT.Mazur.WeierstrassValuationKernelClosureFlat

/-!
# Finiteness of the actual kernel closure over the original valuation ring

Generic-fiber recovery, properness, and proved flatness imply finiteness of the
same schematic closure. No splitting field, integral point enumeration, or
finite-flat substitute is assumed at the original base.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false

variable {R K : Type} [CommRing R] [IsDomain R] [ValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  (W : WeierstrassCurve R) {H : Scheme}
  (i : H ⟶ integralCurve (W.map (algebraMap R K))) [IsClosedImmersion i]
  [Flat (i ≫ integralCurveStructure (W.map (algebraMap R K)))]
  [IsFinite (i ≫ integralCurveStructure (W.map (algebraMap R K)))]

/-- The constructed original closure is finite, including when its generic kernel is nonsplit. -/
theorem genericKernelClosureStructure_finite_valuation :
    IsFinite (genericKernelClosureStructure W i) := by
  let _ : Flat (genericKernelClosureStructure W i) :=
    genericKernelClosureStructure_flat_bezout W i
  let _ : IsFinite (pullback.snd (genericKernelClosureStructure W i)
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))) := by
    rw [← (genericKernelClosureStructure_isPullback W i).isoPullback_inv_snd]
    infer_instance
  exact ProperFlatValuationFinite.finite_of_generic (K := K) (genericKernelClosureStructure W i)

/-- The original finite flat generic kernel has its constructed finite flat integral closure. -/
theorem genericKernelClosureStructure_finite_flat :
    IsFinite (genericKernelClosureStructure W i) ∧ Flat (genericKernelClosureStructure W i) :=
  ⟨genericKernelClosureStructure_finite_valuation W i,
    genericKernelClosureStructure_flat_bezout W i⟩

end FLT.Mazur.WeierstrassIntegralChart

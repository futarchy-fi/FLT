/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassValuationKernelClosureFinite
public import FLT.Mazur.FiniteLocallyFreeDegreeAffine

/-!
# The original integral kernel closure retains its generic degree

Over a Noetherian valuation base the constructed finite flat closure is locally
of finite presentation. Its rank is constant on the connected original base,
and generic-fiber recovery identifies that constant with the original degree.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false

variable {R K : Type} [CommRing R] [IsDomain R] [ValuationRing R] [IsNoetherianRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  (W : WeierstrassCurve R) {H : Scheme}
  (i : H ⟶ integralCurve (W.map (algebraMap R K))) [IsClosedImmersion i]

/-- The actual closure has the same finite locally free degree as the original generic kernel. -/
theorem genericKernelClosureStructure_degree (n : ℕ)
    (hd : FCurve.FiniteLocallyFreeDegree
      (i ≫ integralCurveStructure (W.map (algebraMap R K))) n) :
    FCurve.FiniteLocallyFreeDegree (genericKernelClosureStructure W i) n := by
  let _ : IsFinite (i ≫ integralCurveStructure (W.map (algebraMap R K))) := hd.1
  let _ : Flat (i ≫ integralCurveStructure (W.map (algebraMap R K))) := hd.2.1
  let _ : IsFinite (genericKernelClosureStructure W i) :=
    genericKernelClosureStructure_finite_valuation W i
  let _ : Flat (genericKernelClosureStructure W i) :=
    genericKernelClosureStructure_flat_bezout W i
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  intro x
  let y := IsLocalRing.closedPoint K
  have he := Scheme.Hom.finrank_of_isPullback _ _ _ _
    (genericKernelClosureStructure_isPullback W i) y
  calc
    (genericKernelClosureStructure W i).finrank x =
        (genericKernelClosureStructure W i).finrank
          (Spec.map (CommRingCat.ofHom (algebraMap R K)) y) :=
      (genericKernelClosureStructure W i).isLocallyConstant_finrank
        |>.apply_eq_of_preconnectedSpace _ _
    _ = n := he.symm.trans (hd.2.2.2 y)

end FLT.Mazur.WeierstrassIntegralChart

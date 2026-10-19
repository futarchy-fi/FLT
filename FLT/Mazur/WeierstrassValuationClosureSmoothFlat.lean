/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGenericClosureSmoothRecovery
public import FLT.Mazur.WeierstrassValuationKernelClosureFinite
public import FLT.Mazur.SchemeFlatProductDensity

/-!
# Flatness and dense generic pairs on the original smooth kernel intersection

The finite flat closure supplies flatness and local quasi-finiteness of its
actual smooth intersection. Its generic pairs detect all equations on the
integral product; this is the descent input for subgroup multiplication.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false

variable {R K : Type} [CommRing R] [IsDomain R] [ValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  (W : WeierstrassCurve R) (hΔ : IsUnit (W.map (algebraMap R K)).Δ)
  {H : Scheme} (i : H ⟶ integralCurve (W.map (algebraMap R K))) [IsClosedImmersion i]
  [Flat (i ≫ integralCurveStructure (W.map (algebraMap R K)))]

/-- The original smooth intersection is flat over the original valuation base. -/
theorem genericClosureSmoothStructure_flat_valuation :
    Flat (genericClosureSmoothStructure W i) := by
  let _ := genericKernelClosureStructure_flat_bezout W i
  infer_instance

/-- The actual smooth intersection has zero-dimensional fibers over the valuation base. -/
theorem genericClosureSmoothStructure_locallyQuasiFinite
    [IsFinite (i ≫ integralCurveStructure (W.map (algebraMap R K)))] :
    LocallyQuasiFinite (genericClosureSmoothStructure W i) := by
  let _ := genericKernelClosureStructure_finite_valuation W i
  exact inferInstanceAs
    (LocallyQuasiFinite (genericClosureSmoothToClosure W i ≫ genericKernelClosureStructure W i))

omit [IsDomain R] [ValuationRing R] in
/-- The original generic map to the actual smooth intersection is flat over the integral base. -/
theorem genericKernelToClosureSmooth_structure_flat :
    Flat (genericKernelToClosureSmooth W hΔ i ≫ genericClosureSmoothStructure W i) := by
  let _ : Flat (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
    Flat.SpecMap_iff.mpr
      (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R)))
  rw [(genericClosureSmoothStructure_isPullback W hΔ i).w]
  infer_instance

/-- The original generic pairs map to the product of the actual smooth intersections. -/
def genericClosureSmoothPairMap :
    pullback (genericKernelToClosureSmooth W hΔ i ≫ genericClosureSmoothStructure W i)
      (genericKernelToClosureSmooth W hΔ i ≫ genericClosureSmoothStructure W i) ⟶
        pullback (genericClosureSmoothStructure W i) (genericClosureSmoothStructure W i) :=
  pullback.map _ _ _ _ (genericKernelToClosureSmooth W hΔ i)
    (genericKernelToClosureSmooth W hΔ i) (𝟙 _) (by simp) (by simp)

/-- The original generic pairs detect every equation on the integral smooth product. -/
theorem genericClosureSmoothPairMap_dense :
    IsSchemeTheoreticallyDominant (genericClosureSmoothPairMap W hΔ i) := by
  let _ := genericClosureSmoothStructure_flat_valuation W i
  let _ := genericKernelToClosureSmooth_structure_flat W hΔ i
  exact SchemeFlatProductDensity.product_dense _ _ _ _

end FLT.Mazur.WeierstrassIntegralChart

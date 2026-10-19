/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedKernelFinite
public import FLT.Mazur.DenseClosedRestriction

/-!
# Contracting the full divided kernel onto the original closure

Dense equations construct the comparison to the retained original closure.
It preserves the actual original inclusion and generic source, and is proper
and surjective. Over a valuation base with finite flat generic kernel it is finite.
No isomorphism of the two integral closures is assumed.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false

variable {R K : Type} [CommRing R] [IsDomain R] [IsBezout R]
  [Field K] [Algebra R K]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
  (hΔ : IsUnit (W.map (algebraMap R K)).Δ)
  {H : Scheme} (i : H ⟶ integralCurve (W.map (algebraMap R K))) [IsClosedImmersion i]

/-- The concrete contraction restricted to the full kernel closures. -/
def finiteGlobalKernelClosureContraction :
    finiteGlobalKernelClosure hπ data j hj hΔ i ⟶ genericKernelClosure W i :=
  DenseClosedRestriction.lift (finiteGlobalKernelToClosure hπ data j hj hΔ i)
    (genericKernelClosureInclusion W i)
    (finiteGlobalKernelClosureInclusion hπ data j hj hΔ i ≫
      finiteGlobalContraction hπ data j hj) (genericKernelToClosure W i) (by
        rw [finiteGlobalKernelToClosure_inclusion_assoc,
          finiteGlobalGenericCurve_contraction,
          genericKernelToClosure_inclusion])

/-- The comparison preserves the original closed inclusion and concrete contraction. -/
@[reassoc] theorem finiteGlobalKernelClosureContraction_inclusion :
    finiteGlobalKernelClosureContraction hπ data j hj hΔ i ≫ genericKernelClosureInclusion W i =
      finiteGlobalKernelClosureInclusion hπ data j hj hΔ i ≫
        finiteGlobalContraction hπ data j hj :=
  DenseClosedRestriction.lift_inclusion _ _ _ _ _

/-- The comparison retains precisely the original generic kernel map. -/
@[reassoc] theorem finiteGlobalKernelToClosure_contraction :
    finiteGlobalKernelToClosure hπ data j hj hΔ i ≫
      finiteGlobalKernelClosureContraction hπ data j hj hΔ i = genericKernelToClosure W i :=
  DenseClosedRestriction.dense_lift _ _ _ _ _

/-- The comparison is over the exact original integral base. -/
@[reassoc] theorem finiteGlobalKernelClosureContraction_structure :
    finiteGlobalKernelClosureContraction hπ data j hj hΔ i ≫ genericKernelClosureStructure W i =
      finiteGlobalKernelClosureStructure hπ data j hj hΔ i := by
  rw [genericKernelClosureStructure, finiteGlobalKernelClosureContraction_inclusion_assoc]
  rfl

instance finiteGlobalKernelClosureContraction_proper :
    IsProper (finiteGlobalKernelClosureContraction hπ data j hj hΔ i) := by
  let _ : IsProper (finiteGlobalKernelClosureContraction hπ data j hj hΔ i ≫
      genericKernelClosureStructure W i) := by
    rw [finiteGlobalKernelClosureContraction_structure]
    infer_instance
  exact IsProper.of_comp _ (genericKernelClosureStructure W i)

instance finiteGlobalKernelClosureContraction_dense :
    IsSchemeTheoreticallyDominant (finiteGlobalKernelClosureContraction hπ data j hj hΔ i) := by
  constructor
  have he := congrArg Scheme.Hom.ker (finiteGlobalKernelToClosure_contraction hπ data j hj hΔ i)
  simpa only [Scheme.Hom.ker_comp, Scheme.Hom.ker_eq_bot,
    Scheme.IdealSheafData.map_bot] using he

instance finiteGlobalKernelClosureContraction_surjective :
    Surjective (finiteGlobalKernelClosureContraction hπ data j hj hΔ i) := inferInstance

/-- A finite flat original generic kernel gives a finite comparison of the full closures. -/
theorem finiteGlobalKernelClosureContraction_finite [ValuationRing R] [IsFractionRing R K]
    [Flat (i ≫ integralCurveStructure (W.map (algebraMap R K)))]
    [IsFinite (i ≫ integralCurveStructure (W.map (algebraMap R K)))] :
    IsFinite (finiteGlobalKernelClosureContraction hπ data j hj hΔ i) := by
  let _ : IsFinite (finiteGlobalKernelClosureContraction hπ data j hj hΔ i ≫
      genericKernelClosureStructure W i) := by
    rw [finiteGlobalKernelClosureContraction_structure]
    exact finiteGlobalKernelClosureStructure_finite hπ data j hj hΔ i
  exact IsFinite.of_comp _ (genericKernelClosureStructure W i)

end FLT.Mazur.WeierstrassDividedDepth

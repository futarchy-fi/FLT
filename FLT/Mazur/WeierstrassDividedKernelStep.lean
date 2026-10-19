/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedKernelContraction

/-!
# Retain the full kernel through each concrete divided step

The actual successor contraction restricts to the full kernel closures by
schematic density. Both generic maps and the comparison with the original
closure commute. The restriction is proper, surjective, and finite when the
original generic kernel is finite flat over the valuation fraction field.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false

variable {R K : Type} [CommRing R] [IsDomain R] [IsBezout R]
  [Field K] [Algebra R K]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j + 1 ≤ n)
  (hΔ : IsUnit (W.map (algebraMap R K)).Δ)
  {H : Scheme} (i : H ⟶ integralCurve (W.map (algebraMap R K))) [IsClosedImmersion i]
local notation "hj₀" => Nat.le_of_succ_le hj

/-- The actual step restricted to the two full schematic kernel closures. -/
def finiteGlobalKernelClosureStep : finiteGlobalKernelClosure hπ data (j + 1) hj hΔ i ⟶
    finiteGlobalKernelClosure hπ data j hj₀ hΔ i :=
  DenseClosedRestriction.lift (finiteGlobalKernelToClosure hπ data (j + 1) hj hΔ i)
    (finiteGlobalKernelClosureInclusion hπ data j hj₀ hΔ i)
    (finiteGlobalKernelClosureInclusion hπ data (j + 1) hj hΔ i ≫ finiteGlobalStep hπ data j hj)
    (finiteGlobalKernelToClosure hπ data j hj₀ hΔ i) (by
      rw [finiteGlobalKernelToClosure_inclusion_assoc,
        finiteGlobalGenericCurve_step, finiteGlobalKernelToClosure_inclusion])

/-- The restricted step retains the precise ambient successor contraction. -/
@[reassoc] theorem finiteGlobalKernelClosureStep_inclusion :
    finiteGlobalKernelClosureStep hπ data j hj hΔ i ≫
      finiteGlobalKernelClosureInclusion hπ data j hj₀ hΔ i =
        finiteGlobalKernelClosureInclusion hπ data (j + 1) hj hΔ i ≫
          finiteGlobalStep hπ data j hj := DenseClosedRestriction.lift_inclusion _ _ _ _ _

/-- The restricted step keeps the exact original generic kernel source. -/
@[reassoc] theorem finiteGlobalKernelToClosure_step :
    finiteGlobalKernelToClosure hπ data (j + 1) hj hΔ i ≫
      finiteGlobalKernelClosureStep hπ data j hj hΔ i =
        finiteGlobalKernelToClosure hπ data j hj₀ hΔ i :=
  DenseClosedRestriction.dense_lift _ _ _ _ _

/-- Both ways to the original full closure are equal, including its original inclusion. -/
@[reassoc] theorem finiteGlobalKernelClosureStep_contraction :
    finiteGlobalKernelClosureStep hπ data j hj hΔ i ≫
      finiteGlobalKernelClosureContraction hπ data j hj₀ hΔ i =
        finiteGlobalKernelClosureContraction hπ data (j + 1) hj hΔ i := by
  apply (cancel_mono (genericKernelClosureInclusion W i)).mp
  rw [Category.assoc, finiteGlobalKernelClosureContraction_inclusion,
    finiteGlobalKernelClosureStep_inclusion_assoc,
    finiteGlobalStep_contraction, finiteGlobalKernelClosureContraction_inclusion]

/-- The entire kernel step keeps the original integral structure map. -/
@[reassoc] theorem finiteGlobalKernelClosureStep_structure :
    finiteGlobalKernelClosureStep hπ data j hj hΔ i ≫
      finiteGlobalKernelClosureStructure hπ data j hj₀ hΔ i =
        finiteGlobalKernelClosureStructure hπ data (j + 1) hj hΔ i := by
  rw [← finiteGlobalKernelClosureContraction_structure,
    finiteGlobalKernelClosureStep_contraction_assoc, finiteGlobalKernelClosureContraction_structure]

instance finiteGlobalKernelClosureStep_proper :
    IsProper (finiteGlobalKernelClosureStep hπ data j hj hΔ i) := by
  let _ : IsProper (finiteGlobalKernelClosureStep hπ data j hj hΔ i ≫
      finiteGlobalKernelClosureStructure hπ data j hj₀ hΔ i) := by
    rw [finiteGlobalKernelClosureStep_structure]
    infer_instance
  exact IsProper.of_comp _ (finiteGlobalKernelClosureStructure hπ data j hj₀ hΔ i)

instance finiteGlobalKernelClosureStep_dense :
    IsSchemeTheoreticallyDominant (finiteGlobalKernelClosureStep hπ data j hj hΔ i) := by
  constructor
  have he := congrArg Scheme.Hom.ker (finiteGlobalKernelToClosure_step hπ data j hj hΔ i)
  simpa only [Scheme.Hom.ker_comp, Scheme.Hom.ker_eq_bot,
    Scheme.IdealSheafData.map_bot] using he

instance finiteGlobalKernelClosureStep_surjective :
    Surjective (finiteGlobalKernelClosureStep hπ data j hj hΔ i) := inferInstance

/-- Successor comparisons of the full finite flat kernels are finite. -/
theorem finiteGlobalKernelClosureStep_finite [ValuationRing R] [IsFractionRing R K]
    [Flat (i ≫ integralCurveStructure (W.map (algebraMap R K)))]
    [IsFinite (i ≫ integralCurveStructure (W.map (algebraMap R K)))] :
    IsFinite (finiteGlobalKernelClosureStep hπ data j hj hΔ i) := by
  let _ : IsFinite (finiteGlobalKernelClosureStep hπ data j hj hΔ i ≫
      finiteGlobalKernelClosureStructure hπ data j hj₀ hΔ i) := by
    rw [finiteGlobalKernelClosureStep_structure]
    exact finiteGlobalKernelClosureStructure_finite hπ data (j + 1) hj hΔ i
  exact IsFinite.of_comp _ (finiteGlobalKernelClosureStructure hπ data j hj₀ hΔ i)

end FLT.Mazur.WeierstrassDividedDepth

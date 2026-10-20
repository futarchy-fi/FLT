/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedKernelClosureNegation
public import FLT.Mazur.WeierstrassDividedFiniteGlobalNegationStep
public import FLT.Mazur.WeierstrassDividedKernelStep
public import FLT.Mazur.WeierstrassGenericClosureNegation

/-!
# Exact kernel closure comparisons under negation

The restricted inverse commutes with every actual finite successor and the
comparison with the original integral kernel closure. These are equalities
of the original morphisms on the full closures, including special fibers.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R K : Type} [CommRing R] [IsDomain R] [IsBezout R]
  [Field K] [Algebra R K]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
  (hΔ : IsUnit (W.map (algebraMap R K)).Δ)
  {H : Scheme} (i : H ⟶ integralCurve (W.map (algebraMap R K))) [IsClosedImmersion i]
  (neg : H ⟶ H) (hn : neg ≫ i = i ≫ integralCurveNegation (W.map (algebraMap R K)))
local notation "D" => finiteGlobalKernelToClosure hπ data j hj hΔ i
local notation "I" => finiteGlobalKernelClosureInclusion hπ data j hj hΔ i
local notation "N" => finiteGlobalNegation hπ data j hj
local notation "C" => finiteGlobalKernelClosure hπ data j hj hΔ i

/-- The original full closure comparison retains its original inverse. -/
@[reassoc] theorem finiteKernelClosureNegation_contraction :
    finiteKernelClosureNegation hπ data j hj hΔ i neg hn ≫
        finiteGlobalKernelClosureContraction hπ data j hj hΔ i =
      finiteGlobalKernelClosureContraction hπ data j hj hΔ i ≫
        genericClosureNegation W i neg hn := by
  apply (cancel_mono (genericKernelClosureInclusion W i)).mp
  simp only [Category.assoc, finiteGlobalKernelClosureContraction_inclusion,
    finiteKernelClosureNegation_inclusion_assoc, genericClosureNegation_inclusion,
    finiteGlobalKernelClosureContraction_inclusion_assoc, finiteGlobalNegation_contraction]

/-- The full kernel successor maps commute with the constructed inverse at both stages. -/
@[reassoc] theorem finiteKernelClosureNegation_step (hnext : j + 1 ≤ n) :
    finiteKernelClosureNegation hπ data (j + 1) hnext hΔ i neg hn ≫
        finiteGlobalKernelClosureStep hπ data j hnext hΔ i =
      finiteGlobalKernelClosureStep hπ data j hnext hΔ i ≫
        finiteKernelClosureNegation hπ data j (Nat.le_of_succ_le hnext) hΔ i neg hn := by
  apply (cancel_mono
    (finiteGlobalKernelClosureInclusion hπ data j (Nat.le_of_succ_le hnext) hΔ i)).mp
  simp only [Category.assoc, finiteGlobalKernelClosureStep_inclusion,
    finiteKernelClosureNegation_inclusion_assoc, finiteKernelClosureNegation_inclusion,
    finiteGlobalKernelClosureStep_inclusion_assoc, finiteGlobalNegation_step]

end FLT.Mazur.WeierstrassDividedDepth

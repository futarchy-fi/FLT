/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.OneCocycleScalarBoundary
public import FLT.LocalClassFieldTheory.TateTwoExtension

/-!
# The two-extension operation is the cochain cup

The second lift uses the explicit coinduced primitive. Its differential is
`c(g₀,g₁) • z(g₂,...)`, with positive sign, in every nonnegative input degree.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable {k G : Type} [CommRing k] [Group G] (M : Rep.{0} k G) (c : cocycles₂ M)
  {n : ℕ} (z : (Fin n → G) → k)
  (hz : inhomogeneousCochains.d (Rep.trivial k G k) n z = 0)

/-- Cup a two-cocycle on the right with a scalar cochain. -/
def scalarCupTwo : (Fin (n + 2) → G) → M :=
  fun v => z (fun i => v i.succ.succ) • c (v 0, v 1)

include hz in
/-- The differential of the second lift is the embedded ordinary cup cochain. -/
theorem twoCocycle_scalarLift_d :
    (coinducedInclusion M).hom ∘ scalarCupTwo M c z =
      (inhomogeneousCochains (coinducedCoefficients M)).d (n + 1) (n + 2)
        (scalarCupOne (coinducedCoefficients M) (twoCocyclePrimitive M c) z) := by
  funext v
  rw [inhomogeneousCochains.d_def, scalarCupOne_d]
  have hv : inhomogeneousCochains.d (Rep.trivial k G k) n z
    (fun i => v i.succ) = 0 := congrFun hz (fun i => v i.succ)
  rw [hv, zero_smul, sub_zero]
  have hc := congrFun (twoCocyclePrimitive_d M c) (v 0, v 1)
  rw [← hc]
  exact (coinducedInclusion M).hom.toLinearMap.map_smul _ _

include hz in
/-- The ordinary cup cochain is a genuine cocycle in every degree. -/
theorem scalarCupTwo_cycle :
    inhomogeneousCochains.d M (n + 2) (scalarCupTwo M c z) = 0 := by
  have hS := map_cochainsFunctor_shortExact (coinducedCoefficientSequence_shortExact M)
  have h := hS.d_eq_zero_of_f_eq_d_apply (n + 1) (n + 2)
      (scalarCupOne (coinducedCoefficients M) (twoCocyclePrimitive M c) z)
      (scalarCupTwo M c z) (by exact twoCocycle_scalarLift_d M c z hz) (n + 3)
  change (inhomogeneousCochains M).d (n + 2) (n + 3) (scalarCupTwo M c z) = 0 at h
  rw [inhomogeneousCochains.d_def] at h
  exact h

/-- The second ordinary boundary takes the first cup to cup with the original two-cocycle. -/
theorem shiftedCocycle_connecting_scalarCup :
    groupCohomology.δ (coinducedCoefficientSequence_shortExact M) (n + 1) (n + 2) rfl
      (π (shiftedCoefficients M) (n + 1)
        (cocyclesMk (scalarCupOne _ (shiftedTwoCocycle M c) z)
          (scalarCupOne_cycle _ (shiftedTwoCocycle M c) z hz))) =
      π M (n + 2) (cocyclesMk (scalarCupTwo M c z) (scalarCupTwo_cycle M c z hz)) := by
  apply δ_apply (coinducedCoefficientSequence_shortExact M) rfl
    (scalarCupOne _ (shiftedTwoCocycle M c) z)
    (by simpa [coinducedCoefficientSequence, CochainComplex.of.d] using
      scalarCupOne_cycle _ (shiftedTwoCocycle M c) z hz)
    (scalarCupOne (coinducedCoefficients M) (twoCocyclePrimitive M c) z) _
    (scalarCupTwo M c z) (twoCocycle_scalarLift_d M c z hz)
  funext v
  exact (shiftedProjection M).hom.toLinearMap.map_smul _ _

/-- The two-extension operation agrees with the explicit cochain cup in every degree. -/
theorem twoExtensionCohomologyMap_cup :
    twoExtensionCohomologyMap M c n (π (Rep.trivial k G k) n (cocyclesMk z hz)) =
      π M (n + 2) (cocyclesMk (scalarCupTwo M c z) (scalarCupTwo_cycle M c z hz)) :=
  (congrArg (groupCohomology.δ (coinducedCoefficientSequence_shortExact M)
    (n + 1) (n + 2) rfl)
    (oneCocycle_connecting_scalarCup _ (shiftedTwoCocycle M c) z hz)).trans
      (shiftedCocycle_connecting_scalarCup M c z hz)

end LocalClassFieldTheory

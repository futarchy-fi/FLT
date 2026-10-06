/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicInfinityRegular
public import FLT.EllipticCurve.CubicMixedAffine

/-! # Schematic density of finite first inputs in the mixed chart -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The finite-first-input denominator is regular on the whole mixed chart product. -/
theorem mixedFirstZ_mem_nonZeroDivisors :
    mixedFirstZ W ∈ nonZeroDivisors (ChartPairRing W true false) := by
  apply mem_nonZeroDivisors_of_injective
    (Algebra.TensorProduct.comm R (Ring W true) (Ring W false)).injective
  change (1 ⊗ₜ[R] coord W true 1) ∈
    nonZeroDivisors (Ring W false ⊗[R] Ring W true)
  apply mem_nonZeroDivisors_of_injective
    (chartBaseChangeEquiv W (Ring W false) true).injective
  rw [chartBaseChangeEquiv_coord]
  simpa only [map_zero, sub_zero] using
    infinity_v_sub_mem_nonZeroDivisors (W.map (algebraMap R (Ring W false))) 0

theorem mixedAffineRestriction_injective : Function.Injective (mixedAffineRestriction W) :=
  IsLocalization.injective (MixedAffineRing W)
    (Submonoid.powers_le.mpr (mixedFirstZ_mem_nonZeroDivisors W))

/-- Equality on the finite-input part determines a mixed-chart map into a
separated target, without requiring reduced coefficients. -/
instance mixedAffineRestriction_schematic_dominance :
    IsSchemeTheoreticallyDominant
      (Spec.map (CommRingCat.ofHom (mixedAffineRestriction W).toRingHom)) :=
  specMap_schematic_dominance _ (mixedAffineRestriction_injective W)

end WeierstrassCurve.CubicCharts

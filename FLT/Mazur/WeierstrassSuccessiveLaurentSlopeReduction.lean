/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveAdjacentLaurentSlope
public import FLT.Mazur.NilpotentQuadraticDifferenceReduction

/-!
# The two original slopes on a complete Laurent boundary

The small slope reduces to zero and the opposite slope to minus a1.
These reductions hold for every incidence evaluation, retaining all corrections.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (I : Ideal R) (hI : IsNilpotent I) (ha : IsUnit W.a₁) (hs : s ∈ I) (h2 : W.a₂ ∈ I)
  (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
  (f : SuccessiveIncidence.Coordinate π →ₐ[R] R[T;T⁻¹])
local notation "J" => I.map (algebraMap R R[T;T⁻¹])
local notation "v" => nilpotentNodeSlope W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6
local notation "w" => oppositeNodeSlope W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6
local notation "a" => algebraMap R R[T;T⁻¹] W.a₁

/-- The original small slope remains in the coefficient ideal on the whole boundary. -/
theorem laurentSmallSlope_mem : f v ∈ J :=
  incidenceLaurent_ideal π I f
    (nilpotentNodeSlope_mem W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6)

/-- The opposite full slope retains its original residue minus a1. -/
theorem laurentOppositeSlope_add_mem : f w + a ∈ J := by
  have hb : algebraMap R R[T;T⁻¹] b3 * f (SuccessiveIncidence.t π) ∈ J :=
    (J).mul_mem_right _ (Ideal.mem_map_of_mem _ h3)
  have hv := laurentSmallSlope_mem W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6 f
  have h := (J).sub_mem ((J).neg_mem hb) hv
  convert h using 1
  simp only [oppositeNodeSlope, QuadraticRootBranchLocalization.oppositeRoot,
    nodeSlopeLinear, map_sub, map_neg, map_add, map_mul, AlgHom.commutes]
  ring

/-- The full small-branch opposite tangent is invertible, not merely its residue. -/
theorem laurentSmallSlope_add_unit : IsUnit (f v + a) := by
  apply NilpotentQuadraticDifference.isUnit_of_sub_mem I hI
    (algebraMap R R[T;T⁻¹]) (ha.map (algebraMap R R[T;T⁻¹]))
  simpa only [add_sub_cancel_right] using
    laurentSmallSlope_mem W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6 f

/-- The full opposite slope is invertible on the entire original boundary. -/
theorem laurentOppositeSlope_unit : IsUnit (f w) := by
  apply NilpotentQuadraticDifference.isUnit_of_sub_mem I hI
    (algebraMap R R[T;T⁻¹]) (ha.map (algebraMap R R[T;T⁻¹])).neg
  simpa only [sub_neg_eq_add] using
    laurentOppositeSlope_add_mem W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6 f

end FLT.Mazur.WeierstrassSuccessiveX

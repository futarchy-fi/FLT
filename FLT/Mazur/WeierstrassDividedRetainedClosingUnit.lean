/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticStartOneRetained
public import FLT.Mazur.WeierstrassRetainedDepthEdgeUnit
public import FLT.Mazur.WeierstrassRetainedFactorReduction

/-!
# The actual retained closing unit and its tangent reduction

The complete correction remains in the exact formula. Reduction removes
that correction but keeps the tangent raised to twice the retained depth.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m k : ℕ) (hk : k ≤ n) (a : Fin k)
local notation "Q" => Quotient R π m
local notation "L" => Q[T;T⁻¹]
local notation "q" => arithmeticStartOneQuotient W H.a1_unit π m
local notation "V" => arithmeticRetainedFullCorrection data H m k hk a
local notation "A" => zeroInitialTangentUnit (W.map (algebraMap R Q))
  (H.a1_unit.map (algebraMap R Q))
local notation "T₁" => LaurentUnitPoints.pointUnit (AlgHom.id Q L)

/-- The full reciprocal outgoing unit required at the closing edge of either retained arm. -/
def arithmeticRetainedClosingUnit : Lˣ :=
  (retainedFixedEdgeUnit (parameter R π m) q
    (retainedScaledCorrectionUnit (parameter R π m) (retainedDepthScale q 1 a.val) V))⁻¹

/-- The exact parameter retains the complete root correction and the entire tangent power. -/
theorem arithmeticRetainedClosingUnit_eq :
    arithmeticRetainedClosingUnit data H m k hk a =
      Units.map (algebraMap Q L).toMonoidHom (A ^ (2 * (a.val + 1))) * T₁⁻¹ *
        Units.map (leftLaurentMap (parameter R π m)).toMonoidHom V := by
  rw [arithmeticRetainedClosingUnit, retainedFixedEdgeUnit_depth_one_inv,
    arithmeticStartOneQuotient_eq]
  simp only [← inv_pow, inv_inv, ← pow_mul]
  rfl

variable {S : Type} [CommRing S] (f : (Quotient R π m)[T;T⁻¹] →+* S)
  (hf : (ideal (Quotient R π m) (parameter R π m)).map
    (algebraMap (Quotient R π m) (Quotient R π m)[T;T⁻¹]) ≤ RingHom.ker f)
include hf

/-- The entire actual retained correction disappears under reduction of the coefficient ideal. -/
theorem arithmeticRetainedFullCorrection_reduction :
    Units.map (f.comp (leftLaurentMap (parameter R π m)).toRingHom).toMonoidHom V = 1 := by
  unfold arithmeticRetainedFullCorrection
  apply retainedFactorCorrectionUnit_reduction
  apply Ideal.map_le_iff_le_comap.mpr
  intro x hx
  change f (leftLaurentMap (parameter R π m) (algebraMap Q _ x)) = 0
  rw [AlgHom.commutes]
  exact hf (Ideal.mem_map_of_mem _ hx)

/-- The closing parameter reduces to the tangent power times the original reciprocal variable. -/
theorem arithmeticRetainedClosingUnit_reduction :
    Units.map f.toMonoidHom (arithmeticRetainedClosingUnit data H m k hk a) =
      Units.map (f.comp (algebraMap Q L)).toMonoidHom (A ^ (2 * (a.val + 1))) *
        (Units.map f.toMonoidHom T₁)⁻¹ := by
  rw [arithmeticRetainedClosingUnit_eq, map_mul, map_mul, map_inv]
  change _ * _ *
    Units.map (f.comp (leftLaurentMap (parameter R π m)).toRingHom).toMonoidHom V = _
  rw [arithmeticRetainedFullCorrection_reduction data H m k hk a f hf, mul_one]
  rfl

end FLT.Mazur.WeierstrassDividedDepth

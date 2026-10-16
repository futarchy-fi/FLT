/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFixedTerminalReduction
public import FLT.Mazur.WeierstrassDividedRetainedClosingUnit

/-!
# A necessary tangent condition for the proposed closing equality

The second terminal parameter and the recursively normalized retained
parameter have different tangent reductions in general. Their equality
forces an explicit equation on the original coefficient unit.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
local notation "Q" => Quotient R π m
local notation "L" => Q[T;T⁻¹]
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "A" => zeroInitialTangentUnit (W.map (algebraMap R Q))
  (H.a1_unit.map (algebraMap R Q))
local notation "T₁" => LaurentUnitPoints.pointUnit (AlgHom.id Q L)
local notation "v" => fixedTerminalPolygonSecondBoundaryUnit data m j hj
  H.a1_unit (H.scale j) H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "w" => arithmeticRetainedClosingUnit data H m (j + 1) hj
  (Fin.mk j (Nat.lt_succ_self j))
variable {S : Type} [CommRing S] (f : (Quotient R π m)[T;T⁻¹] →+* S)
  (hf : (ideal (Quotient R π m) (parameter R π m)).map
    (algebraMap (Quotient R π m) (Quotient R π m)[T;T⁻¹]) ≤ RingHom.ker f)
local notation "a" => Units.map (RingHom.toMonoidHom (f.comp (algebraMap Q L))) A
include hf

/-- The original second terminal parameter reduces to a1 times the reciprocal variable. -/
theorem arithmeticTerminalSecondUnit_reduction :
    Units.map f.toMonoidHom v = a * (Units.map f.toMonoidHom T₁)⁻¹ := by
  apply Units.ext
  have h := hf (fixedTerminalPolygonSecondBoundaryUnit_sub_tangent_mem data m j hj
    H.a1_unit (H.scale j) H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _))
  change f (_ - _) = 0 at h
  rw [map_sub, map_mul] at h
  change f (v : L) = f (algebraMap Q L (algebraMap R Q W.a₁)) *
    f (LaurentPolynomial.T (-1))
  exact (sub_eq_zero.mp h).trans (mul_comm _ _)

/-- Equality of the actual closing units forces a power equation on the original tangent. -/
theorem arithmeticClosingUnit_eq_tangent_constraint (he : v = w) :
    a = a ^ (2 * (j + 1)) := by
  have h := congrArg (Units.map f.toMonoidHom) he
  rw [arithmeticTerminalSecondUnit_reduction data H m j hj f hf,
    arithmeticRetainedClosingUnit_reduction data H m (j + 1) hj ⟨j, by omega⟩ f hf,
    map_pow] at h
  exact mul_right_cancel h

/-- A failed tangent power equation disproves the proposed full parameter equality. -/
theorem arithmeticClosingUnit_ne_of_tangent
    (ha : a ≠ a ^ (2 * (j + 1))) : v ≠ w := by
  intro he
  exact ha (arithmeticClosingUnit_eq_tangent_constraint data H m j hj f hf he)

/-- At one retained node, a characteristic-zero tangent equal to two rules out equality. -/
theorem arithmeticClosingUnit_ne_of_tangent_two [CharZero S] (hj0 : j = 0)
    (ha : f (algebraMap Q L (algebraMap R Q W.a₁)) = 2) : v ≠ w := by
  apply arithmeticClosingUnit_ne_of_tangent data H m j hj f hf
  intro he
  have h := congrArg Units.val he
  change f (algebraMap Q L (algebraMap R Q W.a₁)) =
    f (algebraMap Q L (algebraMap R Q W.a₁)) ^ (2 * (j + 1)) at h
  rw [ha, hj0] at h
  norm_num at h

end FLT.Mazur.WeierstrassDividedDepth

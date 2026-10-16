/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalBoundaryAlgebra
public import FLT.Mazur.LaurentWeightedInverse

/-!
# Weighted reduction of the actual terminal inverse substitutions

The two scales are constructed in each original arithmetic quotient. Every
annihilator of its parameter removes the full Laurent corrections, even
through the actual inverse substitutions used for terminal normalization.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
open LaurentPolynomial PolygonScaledReciprocal LaurentWeightedInverse WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "L" => Q[T;T⁻¹]
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "A" => zeroInitialTangentUnit (W.map (algebraMap R Q))
  (H.a1_unit.map (algebraMap R Q))
local notation "v" => arithmeticFixedTerminalUnit π W (π ^ (1 + j + 1))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit (H.scale (j + 1)) H.a2_div
  (H.b3_div _) (H.b4_div _) (H.b6_div _) u hu m
local notation "E" => arithmeticTerminalParameterEquiv data H m j hj u hu
local notation "B" => arithmeticRetainedClosingEquiv data H m (j + 1) hj
  (Fin.mk j (Nat.lt_succ_self j))

/-- The original branch tangent coefficient, including the terminal smoothing unit. -/
def arithmeticTerminalTangentCoefficient (b : Bool) : Qˣ :=
  if b then -(v)⁻¹ * A else A

/-- The closed scaling formula lifted using the actual units at each arithmetic order. -/
def arithmeticTerminalTangentScale (b : Bool) : Qˣ :=
  A ^ (2 * (j + 1)) / arithmeticTerminalTangentCoefficient data H m j hj u hu b

/-- The two original full terminal substitutions have precisely these tangent coefficients. -/
theorem arithmeticTerminalParameter_sub_tangent (b : Bool) :
    E b (T 1) - reciprocal (arithmeticTerminalTangentCoefficient data H m j hj u hu b)
      (T 1) ∈ (ideal Q (parameter R π m)).map (algebraMap Q L) := by
  cases b
  · simp only [arithmeticTerminalParameterEquiv, arithmeticTerminalTangentCoefficient,
      Bool.false_eq_true, ↓reduceIte, reciprocal_T]
    rw [show fixedTerminalSecondBoundaryEquiv data m j hj H.a1_unit (H.scale j)
      H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _) (T 1) = _ from
      LaurentScaledNilpotentReparametrization.equiv_T ..]
    change (fixedTerminalPolygonSecondBoundaryUnit data m j hj H.a1_unit (H.scale j)
      H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _) : L) -
        C (A : Q) * T (-1) ∈ _
    rw [mul_comm (C (A : Q))]
    exact fixedTerminalPolygonSecondBoundaryUnit_sub_tangent_mem data m j hj
      H.a1_unit (H.scale j) H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _)
  · simp only [arithmeticTerminalParameterEquiv, arithmeticTerminalTangentCoefficient,
      ↓reduceIte, reciprocal_T]
    rw [show fixedTerminalFirstBoundaryEquiv data m j hj H.a1_unit (H.scale j)
      H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _) u hu (T 1) = _ from
      LaurentScaledNilpotentReparametrization.equiv_T ..]
    change (fixedTerminalPolygonFirstBoundaryUnit data m j hj H.a1_unit (H.scale j)
      H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _) u hu : L) -
        C (↑(-(v)⁻¹ * A) : Q) * T (-1) ∈ _
    exact fixedTerminalFirstUnit_scaled_reduction data m j hj H.a1_unit (H.scale j)
      H.a2_div (H.b3_div _) (H.b4_div _) (H.b6_div _) u hu

/-- Weighted terminal values keep the original tangent while killing only its coefficient error. -/
theorem arithmeticTerminalParameter_weighted (e : Q) (he : e * parameter R π m = 0)
    (b : Bool) (z : L) :
    C e * E b z =
      C e * reciprocal (arithmeticTerminalTangentCoefficient data H m j hj u hu b) z :=
  weighted_hom_of_sub_mem (parameter R π m) e he (E b).toAlgHom _
    (arithmeticTerminalParameter_sub_tangent data H m j hj u hu b) z

omit u hu in
/-- The retained closing substitution has its full depth-dependent weighted tangent power. -/
theorem arithmeticRetainedClosing_weighted (e : Q) (he : e * parameter R π m = 0)
    (z : L) : C e * B z = C e * reciprocal (A ^ (2 * (j + 1))) z := by
  apply weighted_hom_of_sub_mem (parameter R π m) e he (B).toAlgHom _ _ z
  rw [reciprocal_T]
  change B (T 1) - _ ∈ _
  rw [show B (T 1) = _ from LaurentScaledNilpotentReparametrization.equiv_T ..]
  exact arithmeticRetainedClosingUnit_sub_tangent_mem data H m (j + 1) hj
    (Fin.mk j (Nat.lt_succ_self j))

/-- The actual inverse normalization, including all Laurent corrections, has the computed weight. -/
theorem arithmeticTerminalNormalization_weighted (e : Q)
    (he : e * parameter R π m = 0) (b : Bool) (z : L) :
    C e * arithmeticTerminalNormalizationEquiv data H m j hj u hu b z =
      C e * scaling (arithmeticTerminalTangentScale data H m j hj u hu b) z :=
  weighted_normalization e (E b) B _ _
    (arithmeticTerminalParameter_weighted data H m j hj u hu e he b)
    (arithmeticRetainedClosing_weighted data H m j hj e he) z

end FLT.Mazur.WeierstrassDividedDepth

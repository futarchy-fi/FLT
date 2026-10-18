/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroRetainedEdgeAlgebra
public import FLT.Mazur.WeierstrassDividedZeroDiagonalAtlasRestriction

/-!
# The retained edge keeps its full coefficient square and reciprocal residue

The square is recovered from the original whole retained node, cancelling
its open puncture. The residue computation keeps every accumulated factor.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX LaurentPolynomial
open PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => fun k ↦ Quotient R π k
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m

local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "M" => arithmeticInitialMobiusEquiv π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "E" => fun k ↦ arithmeticZeroRetainedEdgeEquiv hπ data H k hj u hu
local notation "D" => arithmeticZeroDiagonalState hπ data H 0 hj u hu
local notation "hD" => arithmeticZeroDiagonalState_compatible hπ data H 0 hj u hu
local notation "ρ" => closingOverlapRestriction (R := R) (π := π) m
local notation "S" => arithmeticZeroDiagonalAtlasRestriction hπ data H hj u hu m

/-- The whole retained edge commutes with the actual arithmetic coefficient map. -/
theorem arithmeticZeroRetainedEdgeEquiv_restriction [IsBezout R] (b : Bool) :
    (coeffMap (restriction R π m).toRingHom).comp (E (m + 1) b).toRingHom =
      (E m b).toRingHom.comp (coeffMap (restriction R π m).toRingHom) := by
  apply (punctureSpecIso_naturality_iff (restriction R π m).toRingHom _ _).mp
  apply (cancel_mono (rightBranchOpen (Q (m + 1)) ((D).last (m + 1) b))).mp
  change ((punctureSpecIso (E m b)).hom ≫ ρ) ≫ _ =
    (ρ ≫ (punctureSpecIso (E (m + 1) b)).hom) ≫ _
  simp only [Category.assoc]
  have hp : rightBranchOpen (Q m) ((D).last m b) ≫ S (.retained ⟨0, by omega⟩ b) =
      ρ ≫ rightBranchOpen (Q (m + 1)) ((D).last (m + 1) b) := by
    rw [arithmeticZeroDiagonalAtlasRestriction_last]
    simpa only [punctureOpen_false, arithmeticZeroDiagonalLastRestriction,
      closingOverlapRestriction] using
      punctureOpen_ringMap (restriction R π m).toRingHom _ _ ((hD).2.1 m b) false
  rw [← hp, ← Category.assoc, arithmeticZeroRetainedEdgeEquiv_side,
    arithmeticZeroInfinityNormalizedRetainedSide_restriction,
    arithmeticZeroRetainedEdgeEquiv_side]

omit [IsDomain R] in
/-- The original full Mobius substitution is reciprocal at order zero. -/
theorem arithmeticZeroMobiusEquiv_residue :
    arithmeticInitialMobiusEquiv π 0 W (π ^ 1)
      (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
        (H.b3_div _) (H.b4_div _) (H.b6_div _) = invert := by
  ext z : 1
  have h := arithmeticInitialMobiusEquiv_sub_mem π 0 W (π ^ 1)
    (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
      (H.b3_div _) (H.b4_div _) (H.b6_div _) z
  have hp : parameter R π 0 = 0 := by
    simpa only [Nat.zero_add, pow_one] using parameter_pow R π 0
  simpa only [hp, ideal, Ideal.span_singleton_zero, Ideal.map_bot,
    Submodule.mem_bot, sub_eq_zero] using h

omit [IsDomain R] in
/-- The original full base substitution is reciprocal at order zero. -/
theorem arithmeticZeroBaseEquiv_residue :
    arithmeticInitialBaseEquiv data H 0 0 hj = invert := by
  ext z : 1
  have h := arithmeticInitialBaseEquiv_sub_mem data H 0 0 hj z
  have hp : parameter R π 0 = 0 := by
    simpa only [Nat.zero_add, pow_one] using parameter_pow R π 0
  simpa only [hp, ideal, Ideal.span_singleton_zero, Ideal.map_bot,
    Submodule.mem_bot, sub_eq_zero] using h

/-- Both exact retained attachments have the required reciprocal seed residue. -/
theorem arithmeticZeroRetainedEdgeEquiv_zero (b : Bool) : E 0 b = invert := by
  simp only [arithmeticZeroRetainedEdgeEquiv, arithmeticZeroRetainedParameterEquiv,
    arithmeticZeroInitialTotalPunctureEquiv_zero, arithmeticFactorRatioLaurentEquiv_zero,
    arithmeticZeroMobiusEquiv_residue data H, arithmeticZeroBaseEquiv_residue data H hj]
  ext z : 1
  exact invert.symm_apply_apply (invert z)

end FLT.Mazur.WeierstrassDividedDepth

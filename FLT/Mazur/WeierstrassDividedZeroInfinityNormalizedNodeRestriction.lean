/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedChartRestriction

/-!
# Both complete source nodes retain the original global quotient

Transport the uncorrected whole-node coefficient arrow through the constructed
node isomorphisms, then identify its restrictions on both full original charts.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFiniteInitialIso arithmeticInitialFactorRatioChart arithmeticZeroFiniteAtlasIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "e" => fun k ↦ arithmeticZeroInfinityNormalizedNodeIso hπ data H k hj u hu
local notation "l" => fun k ↦ arithmeticZeroDiagonalInitialOverlap hπ data H k hj u hu
local notation "i" => fun k ↦ arithmeticZeroDiagonalOverlapToInfinity hπ data H k hj u hu
local notation "S" => arithmeticZeroDiagonalAtlasRestriction hπ data H hj u hu m
local notation "N" => closingNormalizedRestriction data H m
local notation "j" => fun k ↦ arithmeticZeroInfinityNormalizedToGlobal hπ data H k hj u hu
local notation "q" => simultaneousTwistedArithmeticRestriction hπ data H m 0 hj u hu

/-- Both full source node presentations carry the original normalized coefficient quotient. -/
def arithmeticZeroInfinityNormalizedNodeRestriction (b : Bool) :
    arithmeticZeroInfinityNormalizedPushout hπ data H m hj u hu b ⟶
      arithmeticZeroInfinityNormalizedPushout hπ data H (m + 1) hj u hu b :=
  (e m b).hom ≫ N ≫ (e (m + 1) b).inv

local notation "ρ" => arithmeticZeroInfinityNormalizedNodeRestriction hπ data H m hj u hu

/-- The source node arrow commutes with its complete normalized comparison. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedNodeRestriction_node (b : Bool) :
    ρ b ≫ (e (m + 1) b).hom = (e m b).hom ≫ N := by
  simp only [arithmeticZeroInfinityNormalizedNodeRestriction, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- Each complete original initial chart retains its actual corrected source quotient. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedNodeRestriction_initial (b : Bool) :
    pushout.inr (i m) (l m b) ≫ ρ b =
      S (.initial b) ≫ pushout.inr (i (m + 1)) (l (m + 1) b) := by
  apply (cancel_mono (e (m + 1) b).hom).mp
  rw [Category.assoc, arithmeticZeroInfinityNormalizedNodeRestriction_node,
    arithmeticZeroInfinityNormalizedNodeIso_initial_assoc, Category.assoc,
    arithmeticZeroInfinityNormalizedNodeIso_initial,
    arithmeticZeroInfinityNormalizedInitial_restriction]

/-- The common full infinity chart retains its unchanged original source quotient. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedNodeRestriction_infinity (b : Bool) :
    pushout.inl (i m) (l m b) ≫ ρ b =
      S .infinity ≫ pushout.inl (i (m + 1)) (l (m + 1) b) := by
  apply (cancel_mono (e (m + 1) b).hom).mp
  rw [Category.assoc, arithmeticZeroInfinityNormalizedNodeRestriction_node,
    arithmeticZeroInfinityNormalizedNodeIso_infinity_assoc, Category.assoc,
    arithmeticZeroInfinityNormalizedNodeIso_infinity,
    arithmeticZeroInfinityNormalizedBoundary_restriction]

/-- Both entire node arrows are restrictions of the actual original global quotient. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedNodeRestriction_global (b : Bool) :
    ρ b ≫ j (m + 1) b = j m b ≫ q := by
  apply pushout.hom_ext
  · rw [arithmeticZeroInfinityNormalizedNodeRestriction_infinity_assoc,
      arithmeticZeroInfinityNormalizedToGlobal_infinity,
      arithmeticZeroInfinityNormalizedToGlobal_infinity_assoc]
    exact arithmeticZeroDiagonalAtlasChart_restriction hπ data H hj u hu m .infinity
  · rw [arithmeticZeroInfinityNormalizedNodeRestriction_initial_assoc,
      arithmeticZeroInfinityNormalizedToGlobal_initial,
      arithmeticZeroInfinityNormalizedToGlobal_initial_assoc]
    exact arithmeticZeroDiagonalAtlasChart_restriction hπ data H hj u hu m (.initial b)

end FLT.Mazur.WeierstrassDividedDepth

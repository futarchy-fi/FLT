/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SchemeDisjointOpenPair
public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedRetainedPairCharts

/-!
# Both original closing edges as one complete terminal attachment

The disjoint union of the two original punctures is the entire terminal
intersection. Both independent target arrows use the original retained nodes
and their original closing equations.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFiniteAtlasIso simultaneousTwistedArithmeticIso
  arithmeticZeroFiniteInitialIso arithmeticInitialFactorRatioChart
  arithmeticZeroDiagonalAtlasChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "D" => arithmeticZeroDiagonalState hπ data H 0 hj u hu
local notation "s" => PolygonArithmeticSimultaneous.State.last D m
local notation "t" => PolygonArithmeticSimultaneous.State.terminal D m
local notation "l" => fun b ↦ Iso.hom (edgeInversion Q) ≫ leftBranchOpen Q (s b)
local notation "A" => arithmeticZeroDiagonalAtlasObject hπ data H m hj u hu
local notation "c" => arithmeticZeroDiagonalAtlasChart hπ data H m hj u hu
local notation "E" => arithmeticZeroInfinityNormalizedRetainedPairIso hπ data H m hj u hu
local notation "j" => arithmeticZeroInfinityNormalizedRetainedPairToGlobal hπ data H m hj u hu
local notation "f" => arithmeticZeroInfinityNormalizedRetainedPairSourceChart hπ data H m hj u hu
local notation "g" => arithmeticZeroInfinityNormalizedRetainedPairTargetChart hπ data H m hj u hu
local notation "w" => arithmeticZeroInfinityNormalizedRetainedToUnion hπ data H m hj u hu
local notation "r₀" => arithmeticZeroInfinityNormalizedRetainedSide hπ data H m hj u hu
local notation "v" => fun b ↦ pushout.inl (w b) (r₀ b)
local notation "O" => branchTorus Q ⨿ branchTorus Q

/-- Both full original closing punctures enter their one common terminal. -/
def arithmeticZeroInfinityNormalizedTerminalSide : O ⟶ A .terminal :=
  coprod.desc (punctureOpen t false) (punctureOpen t true)

/-- Both original closing edges enter the complete source double attachment. -/
def arithmeticZeroInfinityNormalizedTerminalSource : O ⟶ pushout (v false) (v true) :=
  coprod.desc (l false ≫ f false) (l true ≫ f true)

/-- Both original closing edges enter the independently constructed full target. -/
def arithmeticZeroInfinityNormalizedTerminalTarget : O ⟶ 
    arithmeticZeroInfinityNormalizedRetainedPairTarget hπ data H m hj u hu :=
  coprod.desc (l false ≫ g false) (l true ≫ g true)

local notation "r" => arithmeticZeroInfinityNormalizedTerminalSide hπ data H m hj u hu
local notation "a" => arithmeticZeroInfinityNormalizedTerminalSource hπ data H m hj u hu
local notation "b" => arithmeticZeroInfinityNormalizedTerminalTarget hπ data H m hj u hu

instance arithmeticZeroInfinityNormalizedTerminalSide_isOpenImmersion : IsOpenImmersion r :=
  SchemeDisjointOpenPair.desc_isOpenImmersion _ _
    (arithmeticZeroInfinityNormalizedTerminal_punctures_disjoint hπ data H m hj u hu)

/-- The complete source boundary keeps both original global closing equations. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedTerminalSource_global :
    a ≫ j = r ≫ c .terminal := by
  apply coprod.hom_ext <;>
    simp only [arithmeticZeroInfinityNormalizedTerminalSource,
      arithmeticZeroInfinityNormalizedTerminalSide, coprod.inl_desc_assoc,
      coprod.inr_desc_assoc, Category.assoc,
      arithmeticZeroInfinityNormalizedRetainedPairSourceChart_global,
      arithmeticZeroDiagonalAtlas_closing_normalized]

instance arithmeticZeroInfinityNormalizedTerminalSource_isOpenImmersion : IsOpenImmersion a := by
  have : IsOpenImmersion (a ≫ j) := by
    rw [arithmeticZeroInfinityNormalizedTerminalSource_global]
    infer_instance
  exact IsOpenImmersion.of_comp a j

/-- The whole five-chart comparison respects both entire original closing edges. -/
@[reassoc] theorem arithmeticZeroInfinityNormalizedTerminalSource_comparison :
    a ≫ (E).hom = b := by
  apply coprod.hom_ext <;>
    simp only [arithmeticZeroInfinityNormalizedTerminalSource,
      arithmeticZeroInfinityNormalizedTerminalTarget, coprod.inl_desc,
      coprod.inr_desc, coprod.inl_desc_assoc, coprod.inr_desc_assoc, Category.assoc,
      arithmeticZeroInfinityNormalizedRetainedPairSourceChart_comparison]

instance arithmeticZeroInfinityNormalizedTerminalTarget_isOpenImmersion : IsOpenImmersion b := by
  rw [← arithmeticZeroInfinityNormalizedTerminalSource_comparison]
  infer_instance

/-- The complete original terminal span is a scheme pullback, including both punctures. -/
theorem arithmeticZeroInfinityNormalizedTerminal_isPullback :
    IsPullback a r j (c .terminal) := by
  apply IsOpenImmersion.isPullback _ _ _ _
  · exact (arithmeticZeroInfinityNormalizedTerminalSource_global hπ data H m hj u hu).symm
  · apply TopologicalSpace.Opens.ext
    change c .terminal ⁻¹' Set.range j = Set.range r
    rw [← arithmeticZeroInfinityNormalizedRetainedPairUnionIso_global hπ data H m hj u hu,
      fullChart_iso_comp_range,
      arithmeticZeroInfinityNormalizedTerminal_pair_preimage]
    exact (SchemeDisjointOpenPair.desc_range _ _).symm

end FLT.Mazur.WeierstrassDividedDepth

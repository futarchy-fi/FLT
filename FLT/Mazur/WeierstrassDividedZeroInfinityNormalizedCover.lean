/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroInfinityNodeNormalization
public import FLT.Mazur.WeierstrassDividedZeroDiagonalFirstInfinityIso
public import FLT.Mazur.WeierstrassModificationXOppositeOverlapRange

/-!
# Complete images of the infinity-normalized initial nodes

Each whole original initial/infinity pair covers its full normalized node.
Both orientations have exactly the original full D(q) as their intersection.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
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
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "N" => arithmeticInitialFactorRatioChart π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "P" => arithmeticFactorRatioOverlapParameter π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "E" => arithmeticZeroDiagonalInitialOpenIso hπ data H m hj u hu
local notation "T" => arithmeticZeroDiagonalInitialTotalNodeIso hπ data H m hj u hu
local notation "F" => arithmeticZeroDiagonalInitialFactorRatio hπ data H m hj u hu
local notation "l" => arithmeticZeroDiagonalInitialOverlap hπ data H m hj u hu
local notation "i" => arithmeticZeroDiagonalOverlapToInfinity hπ data H m hj u hu
local notation "V" => arithmeticZeroDiagonalInfinityParameterIso hπ data H m hj u hu
local notation "A" => arithmeticZeroFiniteAtlasObject hπ data H m m hj u hu

local notation "f" => arithmeticZeroInfinityNormalizedInitial hπ data H m hj u hu
local notation "g" => arithmeticZeroInfinityNormalizedBoundary hπ data H m hj u hu
local notation "P₀" => polynomialNodeOverlapInclusion
  (W.map (algebraMap R Q)) (algebraMap R Q (π ^ 1))

omit [IsBezout R] in
/-- The full normalized map is the original factor ratio on the actual source open. -/
theorem arithmeticZeroInfinityNormalizedInitial_eq (b : Bool) :
    f b = (E b).inv ≫ N := by
  apply (cancel_epi (E b).hom).mp
  rw [arithmeticZeroInfinityNormalizedInitial_transport, Iso.hom_inv_id_assoc]

omit [IsBezout R] in
/-- Each complete infinity parameter fills the entire standard right puncture. -/
theorem arithmeticZeroInfinityNormalizedBoundary_range (b : Bool) :
    Set.range (g b) = Set.range (rightBranchOpen Q τ) := by
  unfold arithmeticZeroInfinityNormalizedBoundary
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, Category.id_comp]
    change Set.range (rightBranchOpen Q τ ∘ (V).hom) = _
    exact (V).hom.homeomorph.surjective.range_comp _
  · simp only [↓reduceIte]
    change Set.range (rightBranchOpen Q τ ∘ ((edgeInversion Q).hom ∘ (V).hom)) = _
    exact ((edgeInversion Q).hom.homeomorph.surjective.comp
      (V).hom.homeomorph.surjective).range_comp _

omit [IsBezout R] in
/-- The full opposite source overlap retains the same standard puncture image. -/
theorem arithmeticZeroInfinityNormalizedOverlap_range (b : Bool) :
    Set.range (l b) = Set.range (P₀ ≫ (E b).hom) := by
  cases b
  · rfl
  · change Set.range ((E true).hom ∘ _) = Set.range ((E true).hom ∘ P₀)
    rw [Set.range_comp, Set.range_comp]
    congr 1
    exact polynomialNodeOverlapOpposite_range ..

omit [IsBezout R] in
/-- Normalization preserves the full original intersection, including its nilpotent structure. -/
theorem arithmeticZeroInfinityNormalized_preimage (b : Bool) :
    f b ⁻¹' Set.range (g b) = Set.range (l b) := by
  rw [arithmeticZeroInfinityNormalizedBoundary_range,
    arithmeticZeroInfinityNormalizedOverlap_range, arithmeticZeroInfinityNormalizedInitial_eq]
  dsimp only [arithmeticZeroFiniteAtlasObject]
  simpa only [Iso.refl_hom, Category.comp_id] using
    factorRatioIsoTransport_preimage (E b) (Iso.refl _) N (rightBranchOpen Q τ) (𝟙 _) P₀
      (arithmeticInitialFactorRatioChart_right_preimage π m W (π ^ 1)
        (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
          (H.b3_div _) (H.b4_div _) (H.b6_div _))

/-- Both normalized complete initial/infinity squares are actual scheme pullbacks. -/
theorem arithmeticZeroInfinityNormalized_isPullback (b : Bool) :
    IsPullback i (l b) (g b) (f b) := by
  apply IsOpenImmersion.isPullback _ _ _ _
    (arithmeticZeroInfinityNormalized_compatible hπ data H m hj u hu b).symm
  exact TopologicalSpace.Opens.ext
    (arithmeticZeroInfinityNormalized_preimage hπ data H m hj u hu b)

omit [IsBezout R] in
/-- The two original source opens cover the whole normalized node on either arm. -/
theorem arithmeticZeroInfinityNormalized_cover (b : Bool) (x : PolygonSmoothing.chart Q τ) :
    x ∈ Set.range (f b) ∨ x ∈ Set.range (g b) := by
  rw [arithmeticZeroInfinityNormalizedBoundary_range, arithmeticZeroInfinityNormalizedInitial_eq]
  dsimp only [arithmeticZeroFiniteAtlasObject]
  have he : Set.range ((E b).inv ≫ N) = Set.range N :=
    (E b).inv.homeomorph.surjective.range_comp N
  rw [he]
  exact revisedInitialNode_right_cover τ N (arithmeticInitialFactorRatioChart_image data H m) x

end FLT.Mazur.WeierstrassDividedDepth

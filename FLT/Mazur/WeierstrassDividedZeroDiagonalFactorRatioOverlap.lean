/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroDiagonalFactorRatioInfinity
public import FLT.Mazur.WeierstrassDividedZeroDiagonalInfinityIntersection
public import FLT.Mazur.WeierstrassDividedArithmeticFactorRatioOverlapTorus
public import FLT.Mazur.WeierstrassDividedArithmeticFactorRatioAtlasOverlap

/-!
# The full diagonal initial and infinity overlap equations

The original D(q) computes both initial restrictions and the complete infinity
parameter. The first initial/infinity equation follows without an additional
normalization. The other two equations retain the exact transported transition.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFiniteInitialIso arithmeticInitialFactorRatioChart
  arithmeticZeroFiniteAtlasIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "P" => arithmeticFactorRatioOverlapParameter π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "l" => arithmeticZeroDiagonalInitialOverlap hπ data H m hj u hu
local notation "i" => arithmeticZeroDiagonalOverlapToInfinity hπ data H m hj u hu
local notation "f" => arithmeticZeroDiagonalFactorRatioInitialMap hπ data H m hj u hu
local notation "g" => arithmeticZeroDiagonalFactorRatioInfinityMap hπ data H m hj u hu
local notation "B" => arithmeticZeroDiagonalInitialInfinityBoundary hπ data H m hj u hu
local notation "E" => arithmeticZeroDiagonalInfinityParameterIso hπ data H m hj u hu
local notation "J" => arithmeticZeroDiagonalInfinityBoundaryTransition hπ data H m hj u hu

omit [IsBezout R] in
/-- The entire first original D(q) retains its full transported right boundary. -/
@[reassoc] theorem arithmeticZeroDiagonalFactorRatioInitialMap_overlap_first :
    l false ≫ f false = P ≫ B false := by
  simp only [arithmeticZeroDiagonalInitialOverlap, Bool.false_eq_true, ↓reduceIte,
    Category.assoc]
  rw [show (arithmeticZeroFiniteAtlasIso hπ data H m m hj u hu (.initial false)).hom =
      (arithmeticZeroDiagonalInitialOpenIso hπ data H m hj u hu false).hom from rfl,
    arithmeticZeroDiagonalFactorRatioInitialMap_transport,
    arithmeticInitialFactorRatioChart_overlap_first_assoc]
  rfl

omit [IsBezout R] in
/-- The original opposite restriction includes inversion before the full node transport. -/
@[reassoc] theorem arithmeticZeroDiagonalFactorRatioInitialMap_overlap_opposite :
    l true ≫ f true = P ≫ (edgeInversion Q).hom ≫ B true := by
  simp only [arithmeticZeroDiagonalInitialOverlap, ↓reduceIte, Category.assoc]
  rw [show (arithmeticZeroFiniteAtlasIso hπ data H m m hj u hu (.initial true)).hom =
      (arithmeticZeroDiagonalInitialOpenIso hπ data H m hj u hu true).hom from rfl,
    arithmeticZeroDiagonalFactorRatioInitialMap_transport,
    arithmeticInitialFactorRatioChart_overlap_opposite_assoc]
  rfl

/-- The complete infinity isomorphism restricts to the actual original overlap parameter. -/
@[reassoc] theorem arithmeticZeroDiagonalInfinityParameterIso_overlap :
    i ≫ (E).hom = P := by
  simp only [arithmeticZeroDiagonalOverlapToInfinity,
    arithmeticZeroDiagonalInfinityParameterIso, arithmeticZeroDiagonalInfinityOpenIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc,
    infinityFactorRatioIso_hom]
  rw [← arithmeticFactorRatioOverlapInfinity_eq_atlas hπ data H m 1 hj]
  exact arithmeticFullInfinityRatioParameter_overlap π m W (π ^ 1)
    (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.a2_div
      (H.b3_div _) (H.b4_div _) (H.b6_div _)
      (H.a3_div data) (H.a4_div data) (H.a6_div data)
      (Data.factor3 d) (Data.factor4 d) (Data.factor6 d)

/-- The first full source initial/infinity intersection already glues in the actual target. -/
@[reassoc] theorem arithmeticZeroDiagonalFactorRatioInfinityMap_overlap_first :
    i ≫ g = l false ≫ f false := by
  rw [arithmeticZeroDiagonalFactorRatioInfinityMap, ← Category.assoc,
    arithmeticZeroDiagonalInfinityParameterIso_overlap,
    arithmeticZeroDiagonalFactorRatioInitialMap_overlap_first]

omit [IsBezout R] in
/-- The full initial-pair equation keeps the unreduced right-boundary transition. -/
theorem arithmeticZeroDiagonalFactorRatioInitialMap_overlap_iff :
    l false ≫ f false = l true ≫ f true ↔
      P = P ≫ (edgeInversion Q).hom ≫ (J).hom := by
  rw [arithmeticZeroDiagonalFactorRatioInitialMap_overlap_first,
    arithmeticZeroDiagonalFactorRatioInitialMap_overlap_opposite,
    arithmeticZeroDiagonalInitialInfinityBoundary_transition]
  simp only [← Category.assoc]
  exact cancel_mono (B false)

/-- The opposite full infinity equation has exactly the same remaining transition. -/
theorem arithmeticZeroDiagonalFactorRatioInfinityMap_overlap_opposite_iff :
    i ≫ g = l true ≫ f true ↔ P = P ≫ (edgeInversion Q).hom ≫ (J).hom := by
  rw [arithmeticZeroDiagonalFactorRatioInfinityMap_overlap_first,
    arithmeticZeroDiagonalFactorRatioInitialMap_overlap_iff]

end FLT.Mazur.WeierstrassDividedDepth

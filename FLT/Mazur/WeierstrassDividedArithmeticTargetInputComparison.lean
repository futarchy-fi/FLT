/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRetainedTensorProjection
public import FLT.Mazur.WeierstrassDividedSuccessivePairInputComparison
public import FLT.Mazur.WeierstrassDividedArithmeticAtlasPairPresentation
public import FLT.Mazur.WeierstrassDividedOlderUnequalAddition

/-!
# Arithmetic target inputs agree with the original integral atlas pair

The full smooth arithmetic pair maps into the full target pullback. Its two
own-depth contractions are exactly the existing integral atlas-pair input.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
  arithmeticFixedAdjacentTargetCoordinates
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m k : ℕ) (hk : k ≤ n) (i j : ℕ) (hi : i + 2 ≤ k) (hj : j + 2 ≤ k)
local notation "Q" => Quotient R π m
local notation "c" => retainedOlderFormulaIndex k (i + 1) (Nat.lt_of_succ_le hi)
local notation "d" => retainedOlderFormulaIndex k (j + 1) (Nat.lt_of_succ_le hj)
local notation "di" => data ⟨i + 1, Nat.lt_succ_of_le ((Nat.le_succ (i + 1)).trans (hi.trans hk))⟩
local notation "dj" => data ⟨j + 1, Nat.lt_succ_of_le ((Nat.le_succ (j + 1)).trans (hj.trans hk))⟩
local notation "ei" => data ⟨i + 2, Nat.lt_succ_of_le (hi.trans hk)⟩
local notation "ej" => data ⟨j + 2, Nat.lt_succ_of_le (hj.trans hk)⟩
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q k hk
local notation "fa" => (O c).ι ≫ chart c ≫ s
local notation "fb" => (O d).ι ≫ chart d ≫ s
local notation "E" => arithmeticTargetPairSpectrumIso hπ data m k hk i j hi hj
local notation "I" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk i hi
local notation "J" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk j hj
local notation "coords" => tensorIntegralAtlasProjection hπ data Q k hk
local notation "f" => retainedOlderLowerCoordinates hπ data k hk (i + 1) (Nat.lt_of_succ_le hi)
  (i + 1) le_rfl
local notation "g" => retainedOlderLowerCoordinates hπ data k hk (j + 1) (Nat.lt_of_succ_le hj)
  (j + 1) le_rfl
local notation "input" => Spec.map
  (CommRingCat.ofHom (successiveTensorPairInput hπ di ei dj ej Q).toRingHom)
local notation "P" => arithmeticAtlasPairPresentation hπ data m k hk c d
local notation "F" => olderUnequalFormulaInput hπ data k hk (i + 1) (j + 1)
  (by omega) (by omega)

/-- The whole smooth arithmetic pair includes into the unchanged full target pullback. -/
def arithmeticTargetSmoothPairInclusion : pullback fa fb ⟶
    pullback (chart c ≫ s) (chart d ≫ s) :=
  pullback.map _ _ _ _ (O c).ι (O d).ι (𝟙 _)
    (by rw [Category.comp_id]) (by rw [Category.comp_id])

local notation "inc" => arithmeticTargetSmoothPairInclusion hπ data m k hk i j hi hj

omit [IsBezout R] [IsNoetherianRing R] in
/-- The first target contraction is exactly the integral retained-chart contraction. -/
@[reassoc] theorem arithmeticTargetCoordinates_contraction :
    I ≫ Spec.map (CommRingCat.ofHom (successiveTensorInput hπ di ei Q).toRingHom) =
      coords c ≫ f := by
  unfold arithmeticFixedAdjacentTargetCoordinates
  exact arithmeticRetainedTensorIso_contraction hπ data m k hk (i + 1) (Nat.lt_of_succ_le hi)

/-- Both constructions give the identical full divided-pair input. -/
@[reassoc] theorem arithmeticTargetSmoothPair_input : inc ≫ (E).hom ≫ input = P ≫ F := by
  apply unequalPairSpec_hom_ext
  · simp only [Category.assoc]
    rw [successiveTensorPairInput_spec_left,
      arithmeticTargetPairSpectrumIso_left_assoc, olderUnequalFormulaInput_left]
    dsimp only [arithmeticTargetSmoothPairInclusion, pullback.map]
    erw [pullback.lift_fst_assoc, arithmeticTargetCoordinates_contraction]
    dsimp only [arithmeticAtlasPairPresentation]
    rw [atlasPairPresentation_first_assoc]
    simp only [Category.assoc, tensorIntegralAtlasSmoothOpen]
  · simp only [Category.assoc]
    rw [successiveTensorPairInput_spec_right,
      arithmeticTargetPairSpectrumIso_right_assoc, olderUnequalFormulaInput_right]
    dsimp only [arithmeticTargetSmoothPairInclusion, pullback.map]
    erw [pullback.lift_snd_assoc,
      arithmeticTargetCoordinates_contraction hπ data m k hk j hj]
    dsimp only [arithmeticAtlasPairPresentation]
    rw [atlasPairPresentation_second_assoc]
    simp only [Category.assoc, tensorIntegralAtlasSmoothOpen]

end FLT.Mazur.WeierstrassDividedDepth

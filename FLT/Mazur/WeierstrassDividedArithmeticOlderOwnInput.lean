/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderUnequalAddition
public import FLT.Mazur.WeierstrassDividedArithmeticAtlasPairPresentation
public import FLT.Mazur.SchemeArithmeticCoefficientSupport

/-!
# Own-depth retained pair coordinates at every arithmetic order

The source is the relative product of the original full smooth arithmetic
charts. The divided inputs preserve both entire integral projections and
the original arithmetic coefficient point. Every prime contains the uniformizer.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
  retainedOlderLowerCoordinates retainedOlderFormulaIndex
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j ≤ n) (k l : ℕ) (hk : k < j) (hl : l < j)
local notation "a" => retainedOlderFormulaIndex j k hk
local notation "b" => retainedOlderFormulaIndex j l hl
local notation "d" => data ⟨k, Nat.lt_succ_of_le (hk.le.trans hj)⟩
local notation "e" => data ⟨l, Nat.lt_succ_of_le (hl.le.trans hj)⟩
local notation "f" => retainedOlderLowerCoordinates hπ data j hj k hk k le_rfl
local notation "g" => retainedOlderLowerCoordinates hπ data j hj l hl l le_rfl
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "chart" => arithmeticTensorAtlasMap hπ data m j hj
local notation "s" => finiteGlobalArithmeticStructure hπ data j hj m
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q j hj
local notation "fa" => (O a).ι ≫ chart a ≫ s
local notation "fb" => (O b).ι ≫ chart b ≫ s
local notation "coords" => tensorIntegralAtlasProjection hπ data Q j hj
local notation "P" => arithmeticAtlasPairPresentation hπ data m j hj a b
local notation "F" => olderUnequalFormulaInput hπ data j hj k l hk hl

/-- The complete original retained arithmetic pair supplies both divided inputs. -/
def arithmeticOlderOwnFormulaInput :
    pullback fa fb ⟶ Spec (.of (UnequalPairRing d e)) := P ≫ F

local notation "input" => arithmeticOlderOwnFormulaInput hπ data m j hj k l hk hl

/-- The first divided input is the full first retained arithmetic projection. -/
@[reassoc] theorem arithmeticOlderOwnFormulaInput_left :
    input ≫ Spec.map (CommRingCat.ofHom (unequalPairLeft d e).toRingHom) =
      pullback.fst fa fb ≫ (O a).ι ≫ coords a ≫ f := by
  rw [arithmeticOlderOwnFormulaInput, Category.assoc,
    olderUnequalFormulaInput_left]
  dsimp only [arithmeticAtlasPairPresentation]
  rw [atlasPairPresentation_first_assoc]
  rfl

/-- The second divided input retains the full second retained arithmetic projection. -/
@[reassoc] theorem arithmeticOlderOwnFormulaInput_right :
    input ≫ Spec.map (CommRingCat.ofHom (unequalPairRight d e).toRingHom) =
      pullback.snd fa fb ≫ (O b).ι ≫ coords b ≫ g := by
  rw [arithmeticOlderOwnFormulaInput, Category.assoc,
    olderUnequalFormulaInput_right]
  dsimp only [arithmeticAtlasPairPresentation]
  rw [atlasPairPresentation_second_assoc]
  rfl

/-- The full arithmetic pair retains the original quotient coefficient map. -/
@[reassoc] theorem arithmeticOlderOwnFormulaInput_structure :
    input ≫ Spec.map (CommRingCat.ofHom (algebraMap R (UnequalPairRing d e))) =
      pullback.fst fa fb ≫ fa ≫ q := by
  rw [arithmeticOlderOwnFormulaInput, Category.assoc, olderUnequalFormulaInput,
    atlasPairUnequalFormulaInput_structure, finiteResolvedAtlasPairInput_fst_assoc,
    arithmeticAtlasPairPresentation_structure]

/-- Every arithmetic pair prime contains the uniformizer at every quotient order. -/
theorem arithmeticOlderOwnFormulaInput_parameter_mem (p : (pullback fa fb : Scheme)) :
    algebraMap R (UnequalPairRing d e) π ∈ (input p).asIdeal :=
  spectrumInput_parameter_mem π m input (pullback.fst fa fb ≫ fa)
    (by simpa only [Category.assoc] using
      arithmeticOlderOwnFormulaInput_structure hπ data m j hj k l hk hl) p

end FLT.Mazur.WeierstrassDividedDepth

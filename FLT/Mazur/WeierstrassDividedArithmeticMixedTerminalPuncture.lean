/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticRetainedTerminalAddition
public import FLT.Mazur.WeierstrassDividedTerminalTensorProjection
public import FLT.Mazur.WeierstrassDividedSuccessiveTensorPrimeCoordinates

/-!
# Terminal coordinates in the full arithmetic mixed pair

The full-depth terminal formula prime agrees with its original tensor
coordinates. Both coordinates are compared over the entire quotient ring.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j ≤ n) (k l : ℕ) (hk : k < j) (hl : l ≤ j)
local notation "a" => retainedOlderFormulaIndex j k hk
local notation "b" => (1 : Fin (j + 3))
local notation "d" => data ⟨k, Nat.lt_succ_of_le (hk.le.trans hj)⟩
local notation "e" => data ⟨l, Nat.lt_succ_of_le (hl.trans hj)⟩
local notation "next" => data ⟨k + 1, Nat.lt_succ_of_le ((Nat.succ_le_iff.mpr hk).trans hj)⟩
local notation "Q" => Quotient R π m
local notation "chart" => arithmeticTensorAtlasMap hπ data m j hj
local notation "s" => finiteGlobalArithmeticStructure hπ data j hj m
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q j hj
local notation "fa" => (O a).ι ≫ chart a ≫ s
local notation "fb" => (O b).ι ≫ chart b ≫ s
local notation "input" => arithmeticRetainedTerminalFormulaInput hπ data m j hj k l hk hl
local notation "I" => (arithmeticRetainedTensorIso hπ data m j hj k hk).inv
local notation "T" => ScalarExtension W (π ^ (0 + k)) π (next).b3 (next).b4 (next).b6 Q
local notation "u" => tensorCoord W (π ^ (0 + k)) π (next).b3 (next).b4 (next).b6 Q 2
local notation "x" => WeierstrassDilatation.x W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6

local notation "z" => data ⟨j, Nat.lt_succ_of_le hj⟩
local notation "coords" => tensorIntegralAtlasProjection hπ data Q j hj
local notation "E" => finiteDividedTensorAtlasIso hπ data Q j hj
local notation "inputFull" => arithmeticRetainedTerminalFormulaInput hπ data m j hj k j hk le_rfl
local notation "tx" => WeierstrassDilatation.tensorX W (π ^ (0 + j))
  (z).b3 (z).b4 (z).b6 Q
local notation "ty" => WeierstrassDilatation.tensorY W (π ^ (0 + j))
  (z).b3 (z).b4 (z).b6 Q
local notation "x₂" => unequalPairRight d z
  (WeierstrassDilatation.x W (π ^ (0 + j)) (z).b3 (z).b4 (z).b6)
local notation "y₂" => unequalPairRight d z
  (WeierstrassDilatation.y W (π ^ (0 + j)) (z).b3 (z).b4 (z).b6)

/-- Full-depth mixed inputs retain the entire original terminal integral projection. -/
@[reassoc] theorem arithmeticMixedFormulaInput_terminal_full :
    inputFull ≫ Spec.map (CommRingCat.ofHom (unequalPairRight d z).toRingHom) =
      pullback.snd fa fb ≫ (O b).ι ≫ coords b := by
  rw [arithmeticRetainedTerminalFormulaInput_right, terminalLowerCoordinates_self]
  change _ ≫ _ ≫ _ ≫ 𝟙 _ = _
  rw [Category.comp_id]

/-- The full terminal horizontal prime is exactly its original arithmetic tensor prime. -/
theorem arithmeticMixedFormulaInput_terminal_x_iff (p : (pullback fa fb : Scheme)) :
    x₂ ∈ (inputFull p).asIdeal ↔
      tx ∈ ((E).inv ((O b).ι (pullback.snd fa fb p))).asIdeal := by
  have he := congrArg (fun morphism => morphism p)
    (arithmeticMixedFormulaInput_terminal_full hπ data m j hj k hk)
  change PrimeSpectrum.comap (unequalPairRight d z).toRingHom (inputFull p) =
    coords b ((O b).ι (pullback.snd fa fb p)) at he
  change WeierstrassDilatation.x W (π ^ (0 + j)) (z).b3 (z).b4 (z).b6 ∈
    (PrimeSpectrum.comap (unequalPairRight d z).toRingHom (inputFull p)).asIdeal ↔ _
  rw [he, terminalTensorAtlasProjection_x_iff]

/-- The full terminal ordinate also survives in the same arithmetic coordinate prime. -/
theorem arithmeticMixedFormulaInput_terminal_y_iff (p : (pullback fa fb : Scheme)) :
    y₂ ∈ (inputFull p).asIdeal ↔
      ty ∈ ((E).inv ((O b).ι (pullback.snd fa fb p))).asIdeal := by
  have he := congrArg (fun morphism => morphism p)
    (arithmeticMixedFormulaInput_terminal_full hπ data m j hj k hk)
  change PrimeSpectrum.comap (unequalPairRight d z).toRingHom (inputFull p) =
    coords b ((O b).ι (pullback.snd fa fb p)) at he
  change WeierstrassDilatation.y W (π ^ (0 + j)) (z).b3 (z).b4 (z).b6 ∈
    (PrimeSpectrum.comap (unequalPairRight d z).toRingHom (inputFull p)).asIdeal ↔ _
  rw [he, terminalTensorAtlasProjection_y_iff]

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticInitialTerminalFullCoverage
public import FLT.Mazur.WeierstrassDividedArithmeticTerminalSmoothPuncture
public import FLT.Mazur.WeierstrassDividedArithmeticZeroMixedCoverage

/-!
# Full initial/terminal arithmetic coverage throughout the nodal range

Smoothness supplies the full-depth terminal puncture below middle depth.
Together with the unconditional initial puncture this makes the actual
addition domain the entire smooth pair at every positive stage up to middle.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
  retainedInitialFormulaCoordinates terminalLowerCoordinates
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j ≤ n)
local notation "a" => (Fin.succ ⟨j + 1, Nat.lt_succ_self (j + 1)⟩ : Fin (j + 3))
local notation "b" => (1 : Fin (j + 3))
local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "e" => data ⟨j, Nat.lt_succ_of_le hj⟩
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
local notation "P" => arithmeticAtlasPairPresentation hπ data m j hj a b
local notation "F" => initialTerminalUnequalFormulaInput hπ data j hj

local notation "input" => arithmeticInitialTerminalFormulaInput hπ data m j hj
local notation "coords" => tensorIntegralAtlasProjection hπ data Q j hj
local notation "x₁" => unequalPairLeft d e (x W (π ^ (0 + 0)) (d).b3 (d).b4 (d).b6)
local notation "D" => arithmeticInitialTerminalOpen hπ data m j hj
local notation "E" => arithmeticTerminalInitialOpen hπ data m j hj

/-- The full terminal factor retains its original integral coordinate morphism. -/
@[reassoc] theorem arithmeticInitialTerminalFormulaInput_right :
    input ≫ Spec.map (CommRingCat.ofHom (unequalPairRight d e).toRingHom) =
      pullback.snd fa fb ≫ (O b).ι ≫ coords b := by
  rw [arithmeticInitialTerminalFormulaInput, Category.assoc,
    initialTerminalUnequalFormulaInput, atlasPairUnequalFormulaInput_right]
  dsimp only [arithmeticAtlasPairPresentation]
  rw [atlasPairPresentation_second_assoc]
  rw [terminalLowerCoordinates_self]
  change _ ≫ _ ≫ _ ≫ 𝟙 _ = _
  rw [Category.comp_id]
  rfl

local notation "x₂" => unequalPairRight d e (x W (π ^ (0 + j)) (e).b3 (e).b4 (e).b6)

/-- Smoothness of the terminal input supplies the required nodal puncture. -/
theorem arithmeticInitialTerminalFormulaInput_nodal_punctured [IsLocalRing R] {depth : ℕ}
    (node : SplitNodeDepth W π depth) (hj0 : 0 < j) (hm : 2 * j < depth)
    (p : (pullback fa fb : Scheme)) : x₂ ∉ (input p).asIdeal := by
  have he := congrArg (fun morphism => morphism p)
    (arithmeticInitialTerminalFormulaInput_right hπ data m j hj)
  change PrimeSpectrum.comap (unequalPairRight d e).toRingHom (input p) =
    coords b ((O b).ι (pullback.snd fa fb p)) at he
  change x W (π ^ (0 + j)) (e).b3 (e).b4 (e).b6 ∉
    (PrimeSpectrum.comap (unequalPairRight d e).toRingHom (input p)).asIdeal
  rw [he]
  exact arithmeticTerminalProjection_nodal_punctured hπ data m j hj node
    (by omega) (by omega) _ (pullback.snd fa fb p).property

/-- All positive stages up to the middle have a full initial/terminal output domain. -/
theorem arithmeticInitialTerminalOpen_le_middle_eq_top [IsLocalRing R] {depth : ℕ}
    (node : SplitNodeDepth W π depth) (hj0 : 0 < j) (hm : 2 * j ≤ depth) : D = ⊤ := by
  rcases lt_or_eq_of_le hm with h | h
  · apply top_unique
    intro p _
    exact arithmeticInitialTerminalOpen_nodal_mem node data m j hj hj0 h p
      (arithmeticInitialTerminalFormulaInput_punctured hπ data m j hj p)
      (arithmeticInitialTerminalFormulaInput_nodal_punctured hπ data m j hj node hj0 h p)
  · exact arithmeticInitialTerminalOpen_middle_eq_top hπ data m j hj node hj0 h

/-- Reversing the original full smooth factors also has no remaining domain restriction. -/
theorem arithmeticTerminalInitialOpen_le_middle_eq_top [IsLocalRing R] {depth : ℕ}
    (node : SplitNodeDepth W π depth) (hj0 : 0 < j) (hm : 2 * j ≤ depth) : E = ⊤ := by
  change (pullbackSymmetry fb fa).hom ⁻¹ᵁ D = ⊤
  rw [arithmeticInitialTerminalOpen_le_middle_eq_top hπ data m j hj node hj0 hm]
  rfl

end FLT.Mazur.WeierstrassDividedDepth

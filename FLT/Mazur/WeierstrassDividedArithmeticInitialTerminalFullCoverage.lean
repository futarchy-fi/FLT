/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticInitialTerminalAddition
public import FLT.Mazur.WeierstrassDividedInitialFormulaPuncture
public import FLT.Mazur.WeierstrassDividedArithmeticAtlasRelativeSmooth

/-!
# Unconditional initial/terminal arithmetic coverage at middle depth

The initial formula abscissa is already a unit. Thus the existing mixed
addition domain is the whole smooth pair, in both orders and at every
arithmetic quotient order. No coordinate puncture hypothesis is needed.
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

/-- The first formula input is precisely the entire original initial coordinate projection. -/
@[reassoc] theorem arithmeticInitialTerminalFormulaInput_left :
    input ≫ Spec.map (CommRingCat.ofHom (unequalPairLeft d e).toRingHom) =
      pullback.fst fa fb ≫ (O a).ι ≫ coords a ≫
        retainedInitialFormulaCoordinates data j hj := by
  rw [arithmeticInitialTerminalFormulaInput, Category.assoc,
    initialTerminalUnequalFormulaInput, atlasPairUnequalFormulaInput_left]
  dsimp only [arithmeticAtlasPairPresentation]
  rw [atlasPairPresentation_first_assoc]
  rfl

/-- The original initial input supplies the puncture without an extra assumption. -/
theorem arithmeticInitialTerminalFormulaInput_punctured (p : (pullback fa fb : Scheme)) :
    x₁ ∉ (input p).asIdeal := by
  have he := congrArg (fun morphism => morphism p)
    (arithmeticInitialTerminalFormulaInput_left hπ data m j hj)
  change PrimeSpectrum.comap (unequalPairLeft d e).toRingHom (input p) =
    retainedInitialFormulaCoordinates data j hj
      (coords a ((O a).ι (pullback.fst fa fb p))) at he
  change x W (π ^ (0 + 0)) (d).b3 (d).b4 (d).b6 ∉
    (PrimeSpectrum.comap (unequalPairLeft d e).toRingHom (input p)).asIdeal
  rw [he]
  exact retainedInitialFormulaCoordinates_punctured data j hj _

/-- The middle-depth formula is defined on every original smooth initial/terminal pair. -/
theorem arithmeticInitialTerminalOpen_middle_eq_top [IsLocalRing R] {depth : ℕ}
    (node : SplitNodeDepth W π depth) (hj0 : 0 < j) (hmid : 2 * j = depth) : D = ⊤ := by
  apply top_unique
  intro p _
  exact arithmeticInitialTerminalOpen_middle_mem hπ data m j hj node hj0 hmid p
    (arithmeticInitialTerminalFormulaInput_punctured hπ data m j hj p)

/-- The reverse original order is likewise covered everywhere. -/
theorem arithmeticTerminalInitialOpen_middle_eq_top [IsLocalRing R] {depth : ℕ}
    (node : SplitNodeDepth W π depth) (hj0 : 0 < j) (hmid : 2 * j = depth) : E = ⊤ := by
  apply top_unique
  intro p _
  exact arithmeticTerminalInitialOpen_middle_mem hπ data m j hj node hj0 hmid p
    (arithmeticInitialTerminalFormulaInput_punctured hπ data m j hj _)

local notation "f" => chart a ≫ s
local notation "g" => chart b ≫ s
local instance arithmeticInitialTerminalFullCoverage_structure : LocallyOfFinitePresentation s := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- Every full relatively smooth initial/terminal input reaches the actual addition domain. -/
theorem arithmeticInitialTerminal_middle_target [IsLocalRing R] {depth : ℕ}
    (node : SplitNodeDepth W π depth) (hj0 : 0 < j) (hmid : 2 * j = depth)
    (p : (pullback f g : Scheme))
    (hs : chart a (pullback.fst f g p) ∈ (s).smoothLocus)
    (ht : chart b (pullback.snd f g p) ∈ (s).smoothLocus) :
    ∃ z : (pullback fa fb : Scheme),
      (O a).ι (pullback.fst fa fb z) = pullback.fst f g p ∧
      (O b).ι (pullback.snd fa fb z) = pullback.snd f g p ∧ z ∈ D := by
  obtain ⟨z, hz, he⟩ := arithmeticAtlasRelativePair_exists hπ data m j hj a b p hs ht
  refine ⟨z, hz, he, ?_⟩
  rw [arithmeticInitialTerminalOpen_middle_eq_top hπ data m j hj node hj0 hmid]
  trivial

end FLT.Mazur.WeierstrassDividedDepth

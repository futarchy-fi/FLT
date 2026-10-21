/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticMixedTensorPuncture
public import FLT.Mazur.WeierstrassDividedArithmeticMixedAllMiddleCoverage
public import FLT.Mazur.WeierstrassDividedArithmeticAtlasRelativeSmooth
public import FLT.Mazur.SchemePairSymmetryPoints

/-!
# Full arithmetic mixed coverage from a retained horizontal puncture

At exact middle terminal depth, the actual retained tensor puncture supplies
the existing addition domain. Relatively smooth full arithmetic pairs lift
into that domain while preserving both entire original coordinate points.
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
  (m j : ℕ) (hj : j ≤ n) (k : ℕ) (hk : k < j)
local notation "a" => retainedOlderFormulaIndex j k hk
local notation "b" => (1 : Fin (j + 3))
local notation "next" => data ⟨k + 1, Nat.lt_succ_of_le ((Nat.succ_le_iff.mpr hk).trans hj)⟩
local notation "Q" => Quotient R π m
local notation "chart" => arithmeticTensorAtlasMap hπ data m j hj
local notation "s" => finiteGlobalArithmeticStructure hπ data j hj m
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q j hj
local notation "fa" => (O a).ι ≫ chart a ≫ s
local notation "fb" => (O b).ι ≫ chart b ≫ s
local notation "I" => (arithmeticRetainedTensorIso hπ data m j hj k hk).inv
local notation "u" => tensorCoord W (π ^ (0 + k)) π (next).b3 (next).b4 (next).b6 Q 2

local notation "D" => arithmeticRetainedTerminalOpen hπ data m j hj k j hk le_rfl hk.le
local notation "E" => arithmeticTerminalRetainedOpen hπ data m j hj k j hk le_rfl hk.le
local notation "f" => chart a ≫ s
local notation "g" => chart b ≫ s

/-- The actual horizontal puncture suffices; the terminal factor needs no puncture. -/
theorem arithmeticMixed_horizontal_middle_mem [IsLocalRing R] {depth : ℕ}
    (node : SplitNodeDepth W π depth) (hmid : 2 * j = depth)
    (p : (pullback fa fb : Scheme))
    (hx : u ∉ (I ((O a).ι (pullback.fst fa fb p))).asIdeal) : p ∈ D := by
  apply arithmeticMixed_all_middle_mem hπ data m j hj k hk node hmid p
  exact fun h => hx ((arithmeticMixedFormulaInput_x_iff hπ data m j hj k j hk le_rfl p).mp h)

/-- The reverse mixed order uses the same original horizontal coordinate. -/
theorem arithmeticMixed_reversed_horizontal_middle_mem [IsLocalRing R] {depth : ℕ}
    (node : SplitNodeDepth W π depth) (hmid : 2 * j = depth)
    (p : (pullback fb fa : Scheme))
    (hx : u ∉ (I ((O a).ι (pullback.snd fb fa p))).asIdeal) : p ∈ E := by
  apply arithmeticMixed_horizontal_middle_mem hπ data m j hj k hk node hmid
    ((pullbackSymmetry fb fa).hom p)
  rwa [SchemePairSymmetryPoints.fst_apply]

local instance arithmeticMixedHorizontalCoverage_structure : LocallyOfFinitePresentation s := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- Full relatively smooth mixed inputs reach an actual output domain at every quotient order. -/
theorem arithmeticMixed_horizontal_middle_target [IsLocalRing R] {depth : ℕ}
    (node : SplitNodeDepth W π depth) (hmid : 2 * j = depth)
    (p : (pullback f g : Scheme))
    (hs : chart a (pullback.fst f g p) ∈ (s).smoothLocus)
    (ht : chart b (pullback.snd f g p) ∈ (s).smoothLocus)
    (hx : u ∉ (I (pullback.fst f g p)).asIdeal) :
    ∃ z : (pullback fa fb : Scheme),
      (O a).ι (pullback.fst fa fb z) = pullback.fst f g p ∧
      (O b).ι (pullback.snd fa fb z) = pullback.snd f g p ∧ z ∈ D := by
  obtain ⟨z, hz, he⟩ := arithmeticAtlasRelativePair_exists hπ data m j hj a b p hs ht
  refine ⟨z, hz, he, arithmeticMixed_horizontal_middle_mem
    hπ data m j hj k hk node hmid z ?_⟩
  rwa [hz]

end FLT.Mazur.WeierstrassDividedDepth

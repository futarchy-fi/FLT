/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedIndexed
public import FLT.Mazur.WeierstrassDividedArithmeticTargetSelfFlexiblePreMiddle

/-!
# The two punctured formulas at the last-retained middle boundary

Identify the last-retained coordinate convention with the existing positive
retained formulas. The final stage is only i+2; no further data is requested.
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
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m i : ℕ) (hi : i + 2 ≤ n)
local notation "j" => i + 1
local notation "hj" => hi
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "a" => retainedOlderFormulaIndex (j + 1) j (Nat.lt_succ_self j)
local notation "chart" => arithmeticTensorAtlasMap hπ data m (j + 1) hj
local notation "s" => finiteGlobalArithmeticStructure hπ data (j + 1) hj m
local notation "old" => finiteArithmeticNewestTensorChart hπ data m j hj
local notation "next" => finiteArithmeticDividedTensorChart hπ data m (j + 1) hj
local notation "E" => finiteDividedTensorAtlasIso hπ data Q (j + 1) hj
local notation "f" => chart a ≫ s
local notation "f₀" => old ≫ s
local notation "f'" => next ≫ s
local notation "g'" => chart 1 ≫ s
local notation "coords" => arithmeticLastRetainedIndexedCoordinates node data m j hj



local notation "I" => arithmeticFixedAdjacentTargetCoordinates hπ data m (i + 2) hi i le_rfl
local notation "e" => data ⟨i + 2, Nat.lt_succ_of_le hi⟩
local notation "u" => tensorCoord W (π ^ (0 + (i + 1))) π (e).b3 (e).b4 (e).b6 Q 2
local notation "base" => finiteGlobalStructure hπ data (j + 1) hj
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

omit [IsNoetherianRing R] [IsBezout R] in
/-- The indexed last-retained coordinates equal the existing target coordinates. -/
theorem arithmeticLastRetainedSelf_coordinates : coords = I := by
  unfold arithmeticLastRetainedIndexedCoordinates arithmeticFixedAdjacentTargetCoordinates
  rfl

variable (hm : 2 * (i + 2) = depth)
local notation "V" => arithmeticTargetSelfFlexiblePreMiddleOpen node data m (i + 2) hi i le_rfl
  (by omega) (by omega)
local notation "Z" => arithmeticTargetSelfReciprocalOpen node data m (i + 2) hi i le_rfl

/-- Two existing genuine punctured formula domains in the last-retained pair. -/
def arithmeticLastRetainedSelfPuncturedChart : Bool → (pullback f f).Opens
  | false => V
  | true => Z

local notation "C" => arithmeticLastRetainedSelfPuncturedChart node data m i hi hm

/-- The two formulas retain their whole quotient-valued outputs. -/
def arithmeticLastRetainedSelfPuncturedOutput : (b : Bool) → (C b).toScheme ⟶ pullback q t
  | false => arithmeticTargetSelfFlexiblePreMiddleQuotientOutput
      node data m (i + 2) hi i le_rfl (by omega) (by omega)
  | true => arithmeticTargetSelfReciprocalQuotientOutput node data m (i + 2) hi i le_rfl

/-- The outputs preserve the full arithmetic coefficient morphism. -/
@[reassoc] theorem arithmeticLastRetainedSelfPuncturedOutput_base (b : Bool) :
    arithmeticLastRetainedSelfPuncturedOutput node data m i hi hm b ≫ pullback.fst q t =
      (C b).ι ≫ pullback.fst f f ≫ f := by
  cases b
  · exact arithmeticTargetSelfFlexiblePreMiddleQuotientOutput_base
      node data m (i + 2) hi i le_rfl (by omega) (by omega)
  · exact arithmeticTargetSelfReciprocalQuotientOutput_base node data m (i + 2) hi i le_rfl

/-- Every pair with both original horizontal coordinates nonzero has a formula. -/
theorem arithmeticLastRetainedSelfPuncturedChart_covers (p : (pullback f f : Scheme))
    (hx : u ∉ (coords (pullback.fst f f p)).asIdeal)
    (hy : u ∉ (coords (pullback.snd f f p)).asIdeal) : ∃ b, p ∈ C b := by
  rw [arithmeticLastRetainedSelf_coordinates] at hx hy
  rcases arithmeticTargetSelfFlexiblePreMiddle_punctured_cover
    node data m (i + 2) hi i le_rfl (by omega) (by omega) p hx hy with hp | hp
  · exact ⟨false, hp⟩
  · exact ⟨true, hp⟩

end FLT.Mazur.WeierstrassDividedDepth

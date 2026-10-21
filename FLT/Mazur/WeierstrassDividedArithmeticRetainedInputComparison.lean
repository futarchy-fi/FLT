/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticRetainedDouble
public import FLT.Mazur.WeierstrassDividedArithmeticTargetInputComparison

/-!
# Full divided inputs through the original retained transition

The canonical integral atlas transition and the explicit arithmetic boundary
changes induce exactly the same pair of divided inputs on the smooth source.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
  arithmeticFixedAdjacentBoundarySource arithmeticFixedAdjacentBoundaryTarget
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m k : ℕ) (hk : k ≤ n) (i j : ℕ) (hi : i + 2 ≤ k) (hj : j + 2 ≤ k)
local notation "a" => (Fin.succ ⟨k - i,
  Nat.lt_succ_of_le ((Nat.sub_le k i).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "b" => (Fin.succ ⟨k - j,
  Nat.lt_succ_of_le ((Nat.sub_le k j).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "c" => (Fin.succ ⟨k - (i + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (i + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "d" => (Fin.succ ⟨k - (j + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (j + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "x" => arithmeticFixedAdjacentBoundarySource hπ data m k hk i hi
local notation "z" => arithmeticFixedAdjacentBoundaryTarget hπ data m k hk i hi
local notation "y" => arithmeticFixedAdjacentBoundarySource hπ data m k hk j hj
local notation "w" => arithmeticFixedAdjacentBoundaryTarget hπ data m k hk j hj
local notation "hx" => arithmeticFixedAdjacentBoundary_ambient hπ data m k hk i hi
local notation "hy" => arithmeticFixedAdjacentBoundary_ambient hπ data m k hk j hj

local notation "D" => arithmeticRetainedDoubleOpen hπ data m k hk i j hi hj
local notation "F" => arithmeticRetainedDoubleSmoothOpen hπ data m k hk i j hi hj
local notation "tr" => arithmeticRetainedDoubleTransfer hπ data m k hk i j hi hj
local notation "u₁" => (D).ι ≫ pullback.fst (chart a ≫ s) (chart b ≫ s)
local notation "u₂" => (D).ι ≫ pullback.snd (chart a ≫ s) (chart b ≫ s)
local notation "v₁" => tr ≫ pullback.fst (chart c ≫ s) (chart d ≫ s)
local notation "v₂" => tr ≫ pullback.snd (chart c ≫ s) (chart d ≫ s)
local notation "h" => arithmeticDoubleBoundary_source_base hπ data m k hk a b x y
local notation "h₁" => (arithmeticRetainedDoubleTransfer_first
  hπ data m k hk i j hi hj).symm
local notation "h₂" => (arithmeticRetainedDoubleTransfer_second
  hπ data m k hk i j hi hj).symm
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data
  (PolygonArithmeticStages.Quotient R π m) k hk
local notation "fa" => (O c).ι ≫ chart c ≫ s
local notation "fb" => (O d).ι ≫ chart d ≫ s
local notation "inc" => arithmeticTargetSmoothPairInclusion hπ data m k hk i j hi hj
local notation "P" => arithmeticAtlasPairPresentation hπ data m k hk c d
local notation "transition" => arithmeticRetainedDoubleTransition hπ data m k hk i j hi hj
local notation "transfer" => atlasPairTransfer hπ data k hk a b c d

/-- The entire original smooth transition source supplies the smooth target pair. -/
def arithmeticRetainedSmoothTargetPair : (F).toScheme ⟶ pullback fa fb :=
  arithmeticAtlasTestTarget hπ data m k hk a b c d u₁ u₂ v₁ v₂
    (by simpa only [Category.assoc] using h₁)
    (by simpa only [Category.assoc] using h₂) h

local notation "v" => arithmeticRetainedSmoothTargetPair hπ data m k hk i j hi hj

/-- Its integral presentation is the existing canonical integral atlas transition. -/
@[reassoc] theorem arithmeticRetainedSmoothTargetPair_integral :
    v ≫ P = transition ≫ transfer :=
  (arithmeticRetainedDoubleTransition_target hπ data m k hk i j hi hj).symm

/-- Forgetting smoothness recovers exactly the original arithmetic boundary change. -/
@[reassoc] theorem arithmeticRetainedSmoothTargetPair_inclusion : v ≫ inc = (F).ι ≫ tr := by
  apply pullback.hom_ext
  · apply (cancel_mono (chart c)).mp
    simp only [Category.assoc]
    erw [arithmeticTargetSmoothPairInclusion, pullback.map, pullback.lift_fst_assoc]
    simp only [Category.assoc]
    change v ≫ pullback.fst fa fb ≫ (O c).ι ≫ chart c =
      (F).ι ≫ tr ≫ pullback.fst (chart c ≫ s) (chart d ≫ s) ≫ chart c
    rw [arithmeticRetainedSmoothTargetPair, arithmeticAtlasTestTarget_first,
      arithmeticRetainedDoubleTransfer_first]
    simp only [Category.assoc]
    rfl
  · apply (cancel_mono (chart d)).mp
    simp only [Category.assoc]
    erw [arithmeticTargetSmoothPairInclusion, pullback.map, pullback.lift_snd_assoc]
    simp only [Category.assoc]
    change v ≫ pullback.snd fa fb ≫ (O d).ι ≫ chart d =
      (F).ι ≫ tr ≫ pullback.snd (chart c ≫ s) (chart d ≫ s) ≫ chart d
    rw [arithmeticRetainedSmoothTargetPair, arithmeticAtlasTestTarget_second,
      arithmeticRetainedDoubleTransfer_second]
    simp only [Category.assoc]
    rfl

local notation "di" => data ⟨i + 1, by omega⟩
local notation "dj" => data ⟨j + 1, by omega⟩
local notation "ei" => data ⟨i + 2, by omega⟩
local notation "ej" => data ⟨j + 2, by omega⟩
local notation "E" => arithmeticTargetPairSpectrumIso hπ data m k hk i j hi hj
local notation "input" => Spec.map (CommRingCat.ofHom
  (successiveTensorPairInput hπ di ei dj ej (PolygonArithmeticStages.Quotient R π m)).toRingHom)
local notation "older" => olderUnequalFormulaInput hπ data k hk (i + 1) (j + 1)
  (by omega) (by omega)

/-- Both original transitions give exactly the same full divided-pair morphism. -/
@[reassoc] theorem arithmeticRetainedSmooth_input :
    ((F).ι ≫ tr) ≫ (E).hom ≫ input = (transition ≫ transfer) ≫ older := by
  rw [← arithmeticRetainedSmoothTargetPair_inclusion,
    ← arithmeticRetainedSmoothTargetPair_integral]
  simpa only [Category.assoc, retainedOlderFormulaIndex, Fin.succ] using congrArg (fun f => v ≫ f)
    (arithmeticTargetSmoothPair_input hπ data m k hk i j hi hj)

end FLT.Mazur.WeierstrassDividedDepth

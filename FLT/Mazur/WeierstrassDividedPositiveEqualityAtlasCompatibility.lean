/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCycleAtlasDisjoint
public import FLT.Mazur.WeierstrassDividedPositiveEqualityAtlasFamily
import all FLT.Mazur.WeierstrassDividedPositiveEqualityAtlasFamily

/-!
# Equality-depth overlap equations on the original finite atlas

Diagonal, nonadjacent and deeper retained/infinity overlaps are discharged.
The distinct positive-start initial chart is retained in the index type.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "m" => globalTensorAtlasMap hπ data K (s + 1) hs
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 4) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "d" => positiveEqualityCycleAtlasFamily hπ data D s hs hstart hk hp F w

/-- Compatibility means equality on the actual categorical intersection of the two atlas maps. -/
def PositiveEqualityAtlasCompatible (i j : Fin (s + 1 + 3)) : Prop :=
  pullback.fst (m i) (m j) ≫ d i = pullback.snd (m i) (m j) ≫ d j

/-- A proved overlap equality can be tested on any common scheme over the original chart maps. -/
theorem positiveEqualityAtlasCompatible_on {i j : Fin (s + 1 + 3)}
    (H : PositiveEqualityAtlasCompatible hπ data D s hs hstart hk hp F w i j)
    {V : Scheme.{u}} (a : V ⟶ globalTensorAtlasObject hπ data K (s + 1) hs i)
    (b : V ⟶ globalTensorAtlasObject hπ data K (s + 1) hs j)
    (hab : a ≫ m i = b ≫ m j) : a ≫ d i = b ≫ d j := by
  have h := congrArg (fun f => pullback.lift a b hab ≫ f) H
  simpa only [← Category.assoc, pullback.lift_fst, pullback.lift_snd] using h

/-- Every chart is compatible with itself because its original map is a monomorphism. -/
theorem positiveEqualityAtlasCompatible_self (i : Fin (s + 1 + 3)) :
    PositiveEqualityAtlasCompatible hπ data D s hs hstart hk hp F w i i := by
  apply congrArg (fun f => f ≫ d i)
  exact (cancel_mono (m i)).mp pullback.condition

/-- Reversing the original intersection preserves a proved compatibility equality. -/
theorem positiveEqualityAtlasCompatible_symm {i j : Fin (s + 1 + 3)}
    (H : PositiveEqualityAtlasCompatible hπ data D s hs hstart hk hp F w i j) :
    PositiveEqualityAtlasCompatible hπ data D s hs hstart hk hp F w j i := by
  exact (positiveEqualityAtlasCompatible_on hπ data D s hs hstart hk hp F w H
    (pullback.snd (m j) (m i)) (pullback.fst (m j) (m i)) pullback.condition.symm).symm

/-- Separated retained indices need no additional equation on their cyclic maps. -/
theorem positiveEqualityAtlasCompatible_nonadjacent (i k : Fin (s + 1 + 3))
    (hi : 2 ≤ i.val) (hik : i.val + 2 ≤ k.val) :
    PositiveEqualityAtlasCompatible hπ data D s hs hstart hk hp F w k i := by
  let _ := zeroSplitCycleAtlas_nonadjacent_isEmpty hπ data D s hs i k hi hik
  exact isInitialOfIsEmpty.hom_ext _ _

/-- Every positive retained chart is compatible with the whole infinity chart. -/
theorem positiveEqualityAtlasCompatible_positive_infinity (i : Fin (s + 1 + 3))
    (hi : 2 ≤ i.val) (hil : i.val ≤ s + 1) :
    PositiveEqualityAtlasCompatible hπ data D s hs hstart hk hp F w i 0 := by
  let _ := zeroSplitCycleAtlas_positive_infinity_isEmpty hπ data D s hs i hi hil
  exact isInitialOfIsEmpty.hom_ext _ _

end FLT.Mazur.WeierstrassDividedDepth

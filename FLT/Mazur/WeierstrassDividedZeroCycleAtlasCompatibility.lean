/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCycleAtlasDisjoint
public import FLT.Mazur.WeierstrassDividedZeroCycleAtlasFamily
public import FLT.Mazur.WeierstrassDividedZeroCycleAtlasTerminalSeparation
import all FLT.Mazur.WeierstrassDividedZeroCycleAtlasFamily

/-!
# Proven overlap equalities for the original cyclic atlas family

Diagonal, nonadjacent and positive-depth infinity overlaps are discharged.
The redundant initial chart reduces to infinity through its actual transition.
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
  (hstart : start = 0) (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "m" => globalTensorAtlasMap hπ data K (s + 1) hs
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 3) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "d" => zeroSplitCycleAtlasFamily hπ data D s hs hstart hp F w

/-- Compatibility means equality on the actual categorical intersection of the two atlas maps. -/
def ZeroSplitCycleAtlasCompatible (i j : Fin (s + 1 + 3)) : Prop :=
  pullback.fst (m i) (m j) ≫ d i = pullback.snd (m i) (m j) ≫ d j

/-- A proved overlap equality can be tested on any common scheme over the original chart maps. -/
theorem zeroSplitCycleAtlasCompatible_on {i j : Fin (s + 1 + 3)}
    (H : ZeroSplitCycleAtlasCompatible hπ data D s hs hstart hp F w i j)
    {V : Scheme.{u}} (a : V ⟶ globalTensorAtlasObject hπ data K (s + 1) hs i)
    (b : V ⟶ globalTensorAtlasObject hπ data K (s + 1) hs j)
    (hab : a ≫ m i = b ≫ m j) : a ≫ d i = b ≫ d j := by
  have h := congrArg (fun f => pullback.lift a b hab ≫ f) H
  simpa only [← Category.assoc, pullback.lift_fst, pullback.lift_snd] using h

/-- Every chart is compatible with itself because its original map is a monomorphism. -/
theorem zeroSplitCycleAtlasCompatible_self (i : Fin (s + 1 + 3)) :
    ZeroSplitCycleAtlasCompatible hπ data D s hs hstart hp F w i i := by
  apply congrArg (fun f => f ≫ d i)
  exact (cancel_mono (m i)).mp pullback.condition

/-- Reversing the original intersection preserves a proved compatibility equality. -/
theorem zeroSplitCycleAtlasCompatible_symm {i j : Fin (s + 1 + 3)}
    (H : ZeroSplitCycleAtlasCompatible hπ data D s hs hstart hp F w i j) :
    ZeroSplitCycleAtlasCompatible hπ data D s hs hstart hp F w j i := by
  exact (zeroSplitCycleAtlasCompatible_on hπ data D s hs hstart hp F w H
    (pullback.snd (m j) (m i)) (pullback.fst (m j) (m i)) pullback.condition.symm).symm

/-- Separated retained indices need no additional equation on their cyclic maps. -/
theorem zeroSplitCycleAtlasCompatible_nonadjacent (i k : Fin (s + 1 + 3))
    (hi : 2 ≤ i.val) (hik : i.val + 2 ≤ k.val) :
    ZeroSplitCycleAtlasCompatible hπ data D s hs hstart hp F w k i := by
  let _ := zeroSplitCycleAtlas_nonadjacent_isEmpty hπ data D s hs i k hi hik
  exact isInitialOfIsEmpty.hom_ext _ _

/-- Every positive retained chart is compatible with the whole infinity chart. -/
theorem zeroSplitCycleAtlasCompatible_positive_infinity (i : Fin (s + 1 + 3))
    (hi : 2 ≤ i.val) (hil : i.val ≤ s + 1) :
    ZeroSplitCycleAtlasCompatible hπ data D s hs hstart hp F w i 0 := by
  let _ := zeroSplitCycleAtlas_positive_infinity_isEmpty hπ data D s hs i hi hil
  exact isInitialOfIsEmpty.hom_ext _ _

/-- The entire terminal chart is compatible with infinity, including its node. -/
theorem zeroSplitCycleAtlasCompatible_terminal_infinity :
    ZeroSplitCycleAtlasCompatible hπ data D s hs hstart hp F w (Fin.succ 0) 0 := by
  let _ := zeroSplitCycleAtlas_terminal_infinity_isEmpty hπ data D s hs (by omega) hp
  exact isInitialOfIsEmpty.hom_ext _ _

/-- The original initial/infinity overlap has its prescribed equality of scheme morphisms. -/
theorem zeroSplitCycleAtlasCompatible_initial_infinity :
    ZeroSplitCycleAtlasCompatible hπ data D s hs hstart hp F w ⟨s + 3, by omega⟩ 0 := by
  unfold ZeroSplitCycleAtlasCompatible
  rw [zeroSplitCycleAtlasFamily_initial, zeroSplitCycleAtlasFamily_infinity]
  exact zeroSplitCycleExteriorDesc_compatible hπ data D s hs hstart (by omega) F
    _ _ pullback.condition

/-- Compatibility with infinity implies compatibility with its original initial open chart. -/
theorem zeroSplitCycleAtlasCompatible_initial_of_infinity (i : Fin (s + 1 + 3))
    (H : ZeroSplitCycleAtlasCompatible hπ data D s hs hstart hp F w i 0) :
    ZeroSplitCycleAtlasCompatible hπ data D s hs hstart hp F w i ⟨s + 3, by omega⟩ := by
  let k : Fin (s + 1 + 3) := ⟨s + 3, by omega⟩
  let q := zeroSplitCycleInitialToInfinity hπ data D s hs hstart (by omega)
  have hq : q ≫ m 0 = m k := zeroSplitCycleInitialToInfinity_global
    hπ data D s hs hstart (by omega)
  have he : pullback.fst (m i) (m k) ≫ m i =
      (pullback.snd (m i) (m k) ≫ q) ≫ m 0 := by
    rw [Category.assoc, hq, pullback.condition]
  have h := zeroSplitCycleAtlasCompatible_on hπ data D s hs hstart hp F w H
    (pullback.fst (m i) (m k)) (pullback.snd (m i) (m k) ≫ q) he
  unfold ZeroSplitCycleAtlasCompatible
  rw [zeroSplitCycleAtlasFamily_initial]
  simpa only [Category.assoc, zeroSplitCycleAtlasFamily_infinity,
    zeroSplitCycleInitialDesc] using h

end FLT.Mazur.WeierstrassDividedDepth

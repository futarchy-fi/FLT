/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoSlope
public import FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoTerminalCompatibility
public import FLT.Mazur.WeierstrassDividedLaurentTerminalZeroExclusions
import all FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoTerminalCompatibility
import all FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoSlope
import all FLT.Mazur.WeierstrassDividedZeroEqualityTerminalAtlasDesc
import all FLT.Mazur.WeierstrassDividedZeroEqualityExteriorMaps

/-!
# The four original atlas maps of the length-two equality fiber

Infinity, Laurent, the full horizontal chart and the redundant initial chart
carry one compatible cyclic family. All sixteen original overlaps are checked.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (hs : 0 + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + 0 + 1) ≤ depth)
  (hp : 2 * (start + 0 + 1) = depth)
local notation "K" => ResidueField R
local notation "m" => globalTensorAtlasMap hπ data K (0 + 1) hs
variable {Y : Scheme.{u}}
  (F : Fin 2 → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ j, ProjectiveLine.zero (ResidueField R) ≫ F j =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) j))
/-- The length-two cyclic family on all four original atlas members. -/
def zeroEqualityLengthTwoAtlasFamily (i : Fin 4) :
    (globalTensorOpenCover hπ data K (0 + 1) hs).X i ⟶ Y := by
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.cases ?_ (fun _ => ?_) k) j) i
  · exact zeroEqualityCycleInfinityDesc hπ data D 0 hs hstart hk F
  · exact zeroEqualityCycleTerminalAtlasDesc hπ data D 0 hs hk hp F
  · exact zeroEqualityLengthTwoIndexedDesc hπ data D hs hstart hk hp F w
  · exact zeroEqualityCycleInitialDesc hπ data D 0 hs hstart hk F
local notation "d" => zeroEqualityLengthTwoAtlasFamily hπ data D hs hstart hk hp F w

/-- Compatibility is equality on the actual atlas fiber product. -/
def ZeroEqualityLengthTwoAtlasCompatible (i j : Fin 4) : Prop :=
  pullback.fst (m i) (m j) ≫ d i = pullback.snd (m i) (m j) ≫ d j
local notation "C" => ZeroEqualityLengthTwoAtlasCompatible hπ data D hs hstart hk hp F w

/-- An overlap equality pulls back to every common source. -/
theorem zeroEqualityLengthTwoAtlasCompatible_on {i j : Fin 4} (H : C i j)
    {V : Scheme.{u}} (a : V ⟶ globalTensorAtlasObject hπ data K (0 + 1) hs i)
    (b : V ⟶ globalTensorAtlasObject hπ data K (0 + 1) hs j)
    (hab : a ≫ m i = b ≫ m j) : a ≫ d i = b ≫ d j := by
  have h := congrArg (fun f => pullback.lift a b hab ≫ f) H
  simpa only [← Category.assoc, pullback.lift_fst, pullback.lift_snd] using h

/-- The diagonal overlap is controlled by the original open immersion. -/
theorem zeroEqualityLengthTwoAtlasCompatible_self (i : Fin 4) : C i i := by
  apply congrArg (fun f => f ≫ d i)
  exact (cancel_mono (m i)).mp pullback.condition

/-- Reversing the two original atlas members reverses their compatibility. -/
theorem zeroEqualityLengthTwoAtlasCompatible_symm {i j : Fin 4}
    (H : C i j) : C j i :=
  (zeroEqualityLengthTwoAtlasCompatible_on hπ data D hs hstart hk hp F w H
    (pullback.snd (m j) (m i)) (pullback.fst (m j) (m i)) pullback.condition.symm).symm

/-- The terminal atlas chart misses infinity even at this first modification. -/
theorem zeroEqualityLengthTwoAtlasCompatible_terminal_infinity : C 1 0 := by
  let _ := Scheme.isEmpty_pullback (m 1) (m 0)
    (zeroEqualityAtlas_zero_terminal_infinity_disjoint hπ data D 0 hs hk hp (by omega))
  exact isInitialOfIsEmpty.hom_ext _ _

/-- The original slope boundary proves the horizontal/infinity equation. -/
theorem zeroEqualityLengthTwoAtlasCompatible_infinity_horizontal : C 0 2 :=
  zeroEqualityLengthTwoIndexedDesc_infinity_compatible hπ data D hs hstart hk hp F w

/-- The full conic incidence boundary proves the Laurent/horizontal equation. -/
theorem zeroEqualityLengthTwoAtlasCompatible_terminal_horizontal : C 1 2 :=
  zeroEqualityLengthTwoIndexedDesc_terminal_compatible hπ data D hs hstart hk hp F w

/-- The initial chart is the prescribed restriction of infinity. -/
theorem zeroEqualityLengthTwoAtlasCompatible_initial_infinity : C 3 0 :=
  zeroEqualityCycleExteriorDesc_compatible hπ data D 0 hs hstart hk F
    _ _ pullback.condition

/-- Every compatibility with infinity also holds on its original initial open. -/
theorem zeroEqualityLengthTwoAtlasCompatible_initial_of_infinity (i : Fin 4)
    (H : C i 0) : C i 3 := by
  let q := zeroSplitCycleInitialToInfinity hπ data D 0 hs hstart hk
  have hq : q ≫ m 0 = m 3 := zeroSplitCycleInitialToInfinity_global
    hπ data D 0 hs hstart hk
  have he : pullback.fst (m i) (m 3) ≫ m i =
      (pullback.snd (m i) (m 3) ≫ q) ≫ m 0 := by
    rw [Category.assoc, hq, pullback.condition]
  have h := zeroEqualityLengthTwoAtlasCompatible_on hπ data D hs hstart hk hp F w H
    (pullback.fst (m i) (m 3)) (pullback.snd (m i) (m 3) ≫ q) he
  change _ = _ ≫ zeroEqualityCycleInitialDesc hπ data D 0 hs hstart hk F
  simpa only [Category.assoc, zeroEqualityLengthTwoAtlasFamily, Fin.cases_zero,
    zeroEqualityCycleInitialDesc] using h

/-- All sixteen intersections of the actual length-two atlas are compatible. -/
theorem zeroEqualityLengthTwoAtlasFamily_compatible (i j : Fin 4) : C i j := by
  have h10 := zeroEqualityLengthTwoAtlasCompatible_terminal_infinity
    hπ data D hs hstart hk hp F w
  have h02 := zeroEqualityLengthTwoAtlasCompatible_infinity_horizontal
    hπ data D hs hstart hk hp F w
  have h12 := zeroEqualityLengthTwoAtlasCompatible_terminal_horizontal
    hπ data D hs hstart hk hp F w
  have h30 := zeroEqualityLengthTwoAtlasCompatible_initial_infinity
    hπ data D hs hstart hk hp F w
  have symm {i j : Fin 4} (H : C i j) : C j i :=
    zeroEqualityLengthTwoAtlasCompatible_symm hπ data D hs hstart hk hp F w H
  have h13 := zeroEqualityLengthTwoAtlasCompatible_initial_of_infinity
    hπ data D hs hstart hk hp F w 1 h10
  have h23 := zeroEqualityLengthTwoAtlasCompatible_initial_of_infinity
    hπ data D hs hstart hk hp F w 2 (symm h02)
  fin_cases i <;> fin_cases j
  · exact zeroEqualityLengthTwoAtlasCompatible_self hπ data D hs hstart hk hp F w 0
  · exact symm h10
  · exact h02
  · exact symm h30
  · exact h10
  · exact zeroEqualityLengthTwoAtlasCompatible_self hπ data D hs hstart hk hp F w 1
  · exact h12
  · exact h13
  · exact symm h02
  · exact symm h12
  · exact zeroEqualityLengthTwoAtlasCompatible_self hπ data D hs hstart hk hp F w 2
  · exact h23
  · exact h30
  · exact symm h13
  · exact symm h23
  · exact zeroEqualityLengthTwoAtlasCompatible_self hπ data D hs hstart hk hp F w 3

end FLT.Mazur.WeierstrassDividedDepth

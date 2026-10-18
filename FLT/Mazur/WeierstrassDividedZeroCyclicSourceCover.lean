/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCyclicSourceCharts
public import FLT.Mazur.WeierstrassDividedZeroInfinityNormalizedTerminalIntersection

/-!
# Coverage by the five entire cyclic source nodes

The common infinity and both original initial opens remain in the full union.
Coordinate swaps preserve the complete retained-node images.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] arithmeticZeroDiagonalAtlasChart
  arithmeticZeroInfinityNormalizedFullComparison
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "r" => rightBranchOpen Q τ
local notation "r'" => Iso.hom (edgeInversion Q) ≫ r
local notation "U" => arithmeticZeroInfinityNormalizedFullUnion hπ data H m hj u hu
local notation "F" => arithmeticZeroInfinityNormalizedFullComparison hπ data H m hj u hu
local notation "c" => arithmeticZeroDiagonalAtlasChart hπ data H m hj u hu
local notation "D" => arithmeticZeroDiagonalState hπ data H 0 hj u hu
local notation "f" => arithmeticZeroCyclicSourceChart hπ data H m hj u hu
local notation "a" => arithmeticZeroCyclicInitialChart hπ data H m hj u hu
local notation "X" => simultaneousTwistedArithmeticStage hπ data H m 0 hj u hu

/-- Reflecting either entire retained node preserves its original full global image. -/
theorem arithmeticZeroCyclicSourceChart_retained_range (b : Bool) :
    Set.range (f (.retained b)) = Set.range (c (.retained ⟨0, by omega⟩ b)) := by
  cases b
  · rfl
  · exact fullChart_iso_comp_range (branchSwapIso Q ((D).last m true)) _

/-- Reflecting the opposite initial node preserves the whole normalized node image. -/
theorem arithmeticZeroCyclicSourceChart_initial_range (b : Bool) :
    Set.range (f (.initial b)) = Set.range (a b) := by
  cases b
  · rfl
  · exact fullChart_iso_comp_range (branchSwapIso Q τ) _

/-- Both entire normalized initial nodes cover precisely the original three-chart union. -/
theorem arithmeticZeroCyclicInitialChart_union :
    Set.range (a false) ∪ Set.range (a true) = Set.range (U).ι := by
  ext z
  constructor
  · rintro (⟨x, rfl⟩ | ⟨x, rfl⟩)
    · exact ⟨(F).inv (pushout.inl r r' x), rfl⟩
    · exact ⟨(F).inv (pushout.inr r r' x), rfl⟩
  · rintro ⟨x, rfl⟩
    rcases SchemeOpenPushout.charts_cover r r' ((F).hom x) with ⟨y, hy⟩ | ⟨y, hy⟩
    · left
      refine ⟨y, ?_⟩
      change (U).ι ((F).inv (pushout.inl r r' y)) = (U).ι x
      rw [hy]
      exact congrArg (U).ι (congrArg (fun k ↦ k x) (F).hom_inv_id)
    · right
      refine ⟨y, ?_⟩
      change (U).ι ((F).inv (pushout.inr r r' y)) = (U).ι x
      rw [hy]
      exact congrArg (U).ι (congrArg (fun k ↦ k x) (F).hom_inv_id)

/-- Every point of the original global stage lies on one of the five whole cyclic nodes. -/
theorem arithmeticZeroCyclicSourceChart_cover (z : X) : ∃ i x, f i x = z := by
  have hi (hz : z ∈ Set.range (U).ι) : ∃ i x, f i x = z := by
    rw [← arithmeticZeroCyclicInitialChart_union hπ data H m hj u hu] at hz
    rcases hz with hz | hz
    · exact ⟨.initial false, hz⟩
    · refine ⟨.initial true, ?_⟩
      change z ∈ Set.range (f (.initial true))
      rwa [arithmeticZeroCyclicSourceChart_initial_range]
  have hr (b : Bool) (hz : z ∈ Set.range (c (.retained ⟨0, by omega⟩ b))) :
      ∃ i x, f i x = z := by
    refine ⟨.retained b, ?_⟩
    change z ∈ Set.range (f (.retained b))
    rwa [arithmeticZeroCyclicSourceChart_retained_range]
  rcases arithmeticZeroInfinityNormalizedTerminal_pair_cover hπ data H m hj u hu z with hz | hz
  · change z ∈ Set.range _ at hz
    rw [arithmeticZeroInfinityNormalizedRetainedPairUnion_range] at hz
    rcases hz with (hz | hz) | (hz | hz)
    · exact hi hz
    · exact hr false hz
    · exact hi hz
    · exact hr true hz
  · exact ⟨.terminal, hz⟩

/-- The five full cyclic nodes form an open cover of the actual original stage. -/
def arithmeticZeroCyclicSourceCover : (X).OpenCover :=
  Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) ZeroCyclicVertex
    (fun i ↦ PolygonSmoothing.chart Q
      ((arithmeticZeroCyclicSeed hπ data H hj u hu).parameter m i)) f
    (fun x ↦ by
      obtain ⟨i, y, hy⟩ := arithmeticZeroCyclicSourceChart_cover hπ data H m hj u hu x
      exact ⟨i, y, hy⟩) (fun _ ↦ inferInstance)

/-- Equality on all five whole cyclic nodes detects equality of global source maps. -/
theorem arithmeticZeroCyclicSourceChart_hom_ext {Y : Scheme} (g h : X ⟶ Y)
    (he : ∀ i, f i ≫ g = f i ≫ h) : g = h :=
  (arithmeticZeroCyclicSourceCover hπ data H m hj u hu).hom_ext g h he

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRevisedInitialRetainedReflection
public import FLT.Mazur.WeierstrassDividedRetainedChartOpen
public import FLT.Mazur.WeierstrassDividedRetainedPuncturePreimage
public import FLT.Mazur.WeierstrassDividedRevisedRetainedTargetIntersection
public import FLT.Mazur.WeierstrassDividedRetainedTransport
public import FLT.Mazur.WeierstrassDividedRevisedRetainedNodeMap

/-!
# Reflection of all original retained intersections

Full corrected retained charts retain their exact puncture preimages.
The target classification and unchanged original adjacent squares therefore
reflect every retained/retained equality into the original global stage.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticRetainedFixedSmoothingIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π 1
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 1
local notation "hn" => Fact.mk
  (arithmeticInitialFactorRatioSmoothing_nilpotent W H.a1_unit (π ^ 1) π 1 H.scale_div)
local notation "a" => arithmeticLabeledAtlasMap hπ data H 1 (j + 1) hj
local notation "G" => arithmeticFirstOriginalRevisedChart hπ data H j hj u hu
local notation "C" => arithmeticRetainedFixedSmoothingIso data H 1 (j + 1) hj
local notation "l" => leftBranchOpen Q (parameter R π 1)
local notation "r" => precedingBranch Q (parameter R π 1)

local notation "p" => arithmeticRevisedPolygonParameter data H 1 j hj u hu
local notation "K" => arithmeticFirstResidualRetainedIso hπ data H j hj u hu


attribute [local irreducible] arithmeticFirstOriginalRevisedChart arithmeticRevisedPolygon
  PolygonVariableSmoothing.scheme PolygonVariableSmoothing.chartWithParameter
  arithmeticInitialMobiusSmoothing

omit [IsBezout R] in
/-- Every actual retained equality has its original label and full outgoing puncture. -/
theorem arithmeticFirstRevisedRetained_location (idx other : Fin (j + 1)) (b e : Bool)
    (x y : PolygonSmoothing.chart Q (parameter R π 1))
    (h : G (.retained idx b) x = G (.retained other e) y) :
    (idx = other ∧ b = e) ∨
      (idx.val + 1 = other.val ∧ b = e ∧ x ∈ Set.range l) ∨
      (other.val + 1 = idx.val ∧ b = e ∧ y ∈ Set.range l) := by
  let F := arithmeticFirstRevisedRetainedNodeMap hπ data H j hj u hu
  have hl := revisedRetained_composite_intersection (j + 1) F
    (fun b ↦ (twistedRetainedOrientation data H 1 b).hom)
    (arithmeticRevisedPolygonRetainedChart data H 1 j hj u hu)
    (fun i b ↦ G (.retained i b))
    (arithmeticFirstRevisedRetainedNodeMap_chart hπ data H j hj u hu)
    (Set.range (leftBranchOpen Q τ))
    (arithmeticRevisedRetained_intersection data H 1 j hj u hu) idx other b e x y h
  exact revisedRetained_preimage_transport Q (parameter R π 1) τ (j + 1) F
    (arithmeticFirstRevisedRetainedNodeMap_left hπ data H j hj u hu) idx other b e x y hl

/-- The original adjacent square recovers source equality on the complete outgoing puncture. -/
theorem arithmeticFirstRevisedRetained_adjacent_points_eq (i : ℕ) (hi : i + 1 < j + 1) (b : Bool)
    (x y : PolygonSmoothing.chart Q (parameter R π 1)) (hx : x ∈ Set.range l)
    (h : G (.retained ⟨i, by omega⟩ b) x = G (.retained ⟨i + 1, hi⟩ b) y) :
    a (.retained ⟨i, by omega⟩ b) x = a (.retained ⟨i + 1, hi⟩ b) y := by
  exact fullChartOverlap_points_eq _ _ _ _ l r
    (arithmeticLabeledAtlas_adjacent_isPullback hπ data H 1 (j + 1) hj i hi b).w
    (arithmeticFirstOriginalRevisedChart_adjacent hπ data H j hj u hu i hi b)
    (G (.retained ⟨i + 1, hi⟩ b)).isOpenEmbedding.injective x y hx h

/-- All retained labels reflect equality, including both adjacent orientations and same labels. -/
theorem arithmeticFirstRevisedRetained_points_eq (idx other : Fin (j + 1)) (b e : Bool)
    (x y : PolygonSmoothing.chart Q (parameter R π 1))
    (h : G (.retained idx b) x = G (.retained other e) y) :
    a (.retained idx b) x = a (.retained other e) y := by
  rcases arithmeticFirstRevisedRetained_location hπ data H j hj u hu idx other b e x y h with
    ⟨rfl, rfl⟩ | ⟨hi, rfl, hx⟩ | ⟨hi, rfl, hy⟩
  · exact congrArg (a (.retained idx b)) ((G (.retained idx b)).isOpenEmbedding.injective h)
  · have hlt : idx.val + 1 < j + 1 := by omega
    have hd : other = ⟨idx.val + 1, hlt⟩ := Fin.ext hi.symm
    subst other
    exact arithmeticFirstRevisedRetained_adjacent_points_eq hπ data H j hj u hu
      idx.val hlt b x y hx h
  · have hlt : other.val + 1 < j + 1 := by omega
    have hd : idx = ⟨other.val + 1, hlt⟩ := Fin.ext hi.symm
    subst idx
    exact (arithmeticFirstRevisedRetained_adjacent_points_eq hπ data H j hj u hu
      other.val hlt b y x hy h.symm).symm

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedClosedPolygonSeparation
public import FLT.Mazur.WeierstrassDividedClosedClosingPolygonUnion
public import FLT.Mazur.WeierstrassDividedPolygonTerminalIntersection

/-!
# Reflection of every original retained/terminal equality

The cyclic labels force the last retained depth. The already constructed
embedding of the entire original closing union then reflects equality,
with both full source points and the actual terminal correction retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction

/-- Injectivity on a full open submodel reflects equality of any two points in that open. -/
theorem fullOpen_points_eq {X Y : Scheme} (f : X ⟶ Y) (U : X.Opens)
    (hi : Function.Injective (U.ι ≫ f)) (x y : X) (hx : x ∈ U) (hy : y ∈ U)
    (h : f x = f y) : x = y := by
  exact congrArg U.ι (hi (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) h)

variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π 0
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 0
local notation "hn" => Fact.mk
  (arithmeticInitialFactorRatioSmoothing_nilpotent W H.a1_unit (π ^ 1) π 0 H.scale_div)
local notation "A" => arithmeticLabeledAtlasObject hπ data H 0 (j + 1) hj
local notation "a" => arithmeticLabeledAtlasMap hπ data H 0 (j + 1) hj
local notation "G" => arithmeticClosedPolygonComparisonChart hπ data H j hj u hu
local notation "F" => arithmeticClosedPolygonMap hπ data H j hj u hu

omit [IsBezout R] in
/-- Equality with any terminal point forces the last original retained depth. -/
theorem arithmeticClosedRetainedTerminal_location (idx : Fin (j + 1)) (b : Bool)
    (x : PolygonSmoothing.chart Q (parameter R π 0)) (y : A .terminal)
    (h : G (.retained idx b) x = G .terminal y) : idx.val = j := by
  let _ := hn
  obtain ⟨x', hx⟩ := arithmeticClosedRetained_range_subset hπ data H j hj u hu idx b ⟨x, rfl⟩
  obtain ⟨y', hy⟩ := arithmeticClosedTerminal_range_subset hπ data H j hj u hu ⟨y, rfl⟩
  have hi := retainedPolygon_terminal_location Q τ (j + 1) idx b x' y'
    (hx.trans (h.trans hy.symm))
  omega

/-- The whole original last/terminal pair reflects equality through its open-union embedding. -/
theorem arithmeticClosedLastTerminal_points_eq (b : Bool)
    (x : PolygonSmoothing.chart Q (parameter R π 0)) (y : A .terminal)
    (h : G (.retained ⟨j, Nat.lt_succ_self j⟩ b) x = G .terminal y) :
    a (.retained ⟨j, Nat.lt_succ_self j⟩ b) x = a .terminal y := by
  let U := originalClosingChartUnion hπ data H 0 j hj b
  have hx := congrArg (fun f ↦ f x)
    (arithmeticClosedPolygonMap_chart hπ data H j hj u hu
      (.retained ⟨j, Nat.lt_succ_self j⟩ b))
  have hy := congrArg (fun f ↦ f y)
    (arithmeticClosedPolygonMap_chart hπ data H j hj u hu .terminal)
  exact fullOpen_points_eq F U (U.ι ≫ F).isOpenEmbedding.injective _ _
    (Or.inl ⟨x, rfl⟩) (Or.inr ⟨y, rfl⟩) (hx.trans (h.trans hy.symm))

/-- Every original retained/terminal equality is already an equality in the source stage. -/
theorem arithmeticClosedRetainedTerminal_points_eq (idx : Fin (j + 1)) (b : Bool)
    (x : PolygonSmoothing.chart Q (parameter R π 0)) (y : A .terminal)
    (h : G (.retained idx b) x = G .terminal y) :
    a (.retained idx b) x = a .terminal y := by
  have hi := arithmeticClosedRetainedTerminal_location hπ data H j hj u hu idx b x y h
  have he : idx = ⟨j, Nat.lt_succ_self j⟩ := Fin.ext hi
  subst idx
  exact arithmeticClosedLastTerminal_points_eq hπ data H j hj u hu b x y h

end FLT.Mazur.WeierstrassDividedDepth

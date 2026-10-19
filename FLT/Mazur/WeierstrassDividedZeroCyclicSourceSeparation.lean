/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCyclicSourcePullbacks

/-!
# Nonneighboring entire source nodes are disjoint

The independent standard atlas detects all original source intersections.
Together with the five full edge pullbacks, this excludes every additional overlap.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "S" => arithmeticZeroCyclicSeed hπ data H hj u hu
local notation "D" => arithmeticZeroCyclicDiagonal hπ data H hj u hu
local notation "t" => arithmeticZeroCyclicStandardParameter hπ data H hj u hu m
local notation "N" => arithmeticZeroCyclicNodeIso hπ data H hj u hu m
local notation "P" => arithmeticZeroCyclicPunctureIso hπ data H hj u hu m
local notation "F" => arithmeticZeroCyclicGlobalIso hπ data H m hj u hu
local notation "c" => arithmeticZeroCyclicSourceChart hπ data H m hj u hu
local notation "e" => zeroCyclicIndex

/-- Equality of source points is detected after the full node corrections in the standard atlas. -/
theorem arithmeticZeroCyclicSourceChart_eq_iff (i j : Fin 5)
    (x : PolygonSmoothing.chart Q ((S).parameter m (e i)))
    (y : PolygonSmoothing.chart Q ((S).parameter m (e j))) :
    c (e i) x = c (e j) y ↔
      arithmeticZeroCyclicStandardChart hπ data H hj u hu m i ((N (e i)).hom x) =
        arithmeticZeroCyclicStandardChart hπ data H hj u hu m j ((N (e j)).hom y) := by
  have hi := congrArg (fun f ↦ f x)
    (arithmeticZeroCyclicGlobalIso_chart hπ data H m hj u hu i)
  have hj' := congrArg (fun f ↦ f y)
    (arithmeticZeroCyclicGlobalIso_chart hπ data H m hj u hu j)
  change (F).hom (c (e i) x) = _ at hi
  change (F).hom (c (e j) y) = _ at hj'
  constructor
  · intro h
    exact hi.symm.trans ((congrArg (F).hom h).trans hj')
  · intro h
    exact (F).hom.isOpenEmbedding.injective (hi.trans (h.trans hj'.symm))

/-- Distinct nonneighboring entire source nodes have no points in common. -/
theorem arithmeticZeroCyclicSourceChart_disjoint (i j : Fin 5)
    (hne : i ≠ j) (hij : (finRotate 5).symm i ≠ j) (hji : (finRotate 5).symm j ≠ i) :
    Disjoint (Set.range (c (e i))) (Set.range (c (e j))) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x, rfl⟩ ⟨y, hy⟩
  have he := (arithmeticZeroCyclicSourceChart_eq_iff hπ data H m hj u hu i j x y).mp hy.symm
  rcases (PolygonVariableSmoothing.charts_eq_iff Q 5 t (by decide) hne _ _).mp he with
    ⟨_, hp, _, _⟩ | ⟨_, hp, _, _⟩
  · exact hij hp
  · exact hji hp

end FLT.Mazur.WeierstrassDividedDepth

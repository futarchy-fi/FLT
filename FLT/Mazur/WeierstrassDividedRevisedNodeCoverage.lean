/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRevisedPolygon
public import FLT.Mazur.WeierstrassDividedPolygonLabelCover

/-!
# Full named nodes cover the independent revised polygon

Identifying a node parameter preserves its entire image. Thus the original
terminal, initial and retained labels exhaust the independently glued target.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false

/-- Identifying a node's parameter does not change the image of its full chart. -/
theorem revisedPolygon_chartWithParameter_range {S : Type} [CommRing S]
    (N : ℕ) (p : Fin N → S) [∀ i, Fact (IsNilpotent (p i))] (hN : 2 ≤ N)
    (i : Fin N) (a : S) (ha : a = p i) :
    Set.range (PolygonVariableSmoothing.chartWithParameter S N p hN i a ha) =
      Set.range (PolygonVariableSmoothing.chart S N p hN i) := by
  subst a
  simp only [PolygonVariableSmoothing.chartWithParameter, nodeParameterIso,
    eqToIso_refl, Iso.refl_hom, Category.id_comp]

variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "N" => 2 * (j + 1) + 3
local notation "p" => arithmeticRevisedPolygonParameter data H m j hj u hu
local notation "c" => arithmeticRevisedPolygonChart data H m j hj u hu

/-- The named terminal chart has exactly the raw label-zero image. -/
theorem arithmeticRevisedPolygonTerminalChart_range :
    Set.range (arithmeticRevisedPolygonTerminalChart data H m j hj u hu) = Set.range (c 0) :=
  revisedPolygon_chartWithParameter_range N p (by omega) _ _ _

/-- Each named initial chart preserves the full image of its cyclic label. -/
theorem arithmeticRevisedPolygonInitialChart_range (b : Bool) :
    Set.range (arithmeticRevisedPolygonInitialChart data H m j hj u hu b) =
      Set.range (c (initialPolygonIndex (j + 1) b)) :=
  revisedPolygon_chartWithParameter_range N p (by omega) _ _ _

/-- Each named retained chart preserves the full image of its cyclic label. -/
theorem arithmeticRevisedPolygonRetainedChart_range (a : Fin (j + 1)) (b : Bool) :
    Set.range (arithmeticRevisedPolygonRetainedChart data H m j hj u hu a b) =
      Set.range (c (retainedPolygonIndex (j + 1) a b)) :=
  revisedPolygon_chartWithParameter_range N p (by omega) _ _ _

/-- The full named node families cover every point of the independent target. -/
theorem arithmeticRevisedPolygon_named_cover (x : arithmeticRevisedPolygon data H m j hj u hu) :
    x ∈ Set.range (arithmeticRevisedPolygonTerminalChart data H m j hj u hu) ∨
      (∃ b, x ∈ Set.range (arithmeticRevisedPolygonInitialChart data H m j hj u hu b)) ∨
      ∃ a b, x ∈ Set.range (arithmeticRevisedPolygonRetainedChart data H m j hj u hu a b) := by
  obtain ⟨i, y, hy⟩ := PolygonVariableSmoothing.charts_cover Q N p (by omega) x
  have hx : x ∈ Set.range (c i) := ⟨y, hy⟩
  rcases polygonIndex_cases (j + 1) i with rfl | ⟨b, rfl⟩ | ⟨a, b, rfl⟩
  · exact Or.inl ((arithmeticRevisedPolygonTerminalChart_range data H m j hj u hu).symm ▸ hx)
  · exact Or.inr (Or.inl ⟨b,
      (arithmeticRevisedPolygonInitialChart_range data H m j hj u hu b).symm ▸ hx⟩)
  · exact Or.inr (Or.inr ⟨a, b,
      (arithmeticRevisedPolygonRetainedChart_range data H m j hj u hu a b).symm ▸ hx⟩)

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialPolygonLabels
public import FLT.Mazur.WeierstrassDividedRetainedPolygonMaps

/-!
# Exhaustion of the prescribed polygon labels and the common infinity edge

The terminal, two initial nodes, and both retained arms exhaust the actual
cyclic index set. The two oriented initial infinity edges have the same image.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonSmoothing

/-- Every polygon index is an original terminal, initial, or retained label. -/
theorem polygonIndex_cases (k : ℕ) (i : Fin (2 * k + 3)) :
    i = 0 ∨ (∃ b, i = initialPolygonIndex k b) ∨
      ∃ a b, i = retainedPolygonIndex k a b := by
  by_cases h0 : i.val = 0
  · exact Or.inl (Fin.ext h0)
  by_cases h1 : i.val = k + 1
  · exact Or.inr (Or.inl ⟨false, Fin.ext h1⟩)
  by_cases h2 : i.val = k + 2
  · exact Or.inr (Or.inl ⟨true, Fin.ext h2⟩)
  right; right
  by_cases h : i.val ≤ k
  · refine ⟨⟨k - i.val, by omega⟩, false, Fin.ext ?_⟩
    change i.val = k - (k - i.val)
    omega
  · refine ⟨⟨i.val - (k + 3), by omega⟩, true, Fin.ext ?_⟩
    change i.val = k + 3 + (i.val - (k + 3))
    omega

variable (R : Type*) [CommRing R] (t : R) [Fact (IsNilpotent t)] (k : ℕ)
local notation "c" => PolygonInfinitesimal.chart R t (2 * k + 3) (by omega)
local notation "O" => fun (b : Bool) ↦
  ite (b = true) (Iso.hom (branchSwapIso R t)) (𝟙 (PolygonSmoothing.chart R t))

/-- The opposite initial infinity edge is the original edge with its parameter inverted. -/
@[reassoc] theorem initialPolygon_infinity_edge_true :
    rightBranchOpen R t ≫ (branchSwapIso R t).hom ≫ c (initialPolygonIndex k true) =
      (edgeInversion R).hom ≫ rightBranchOpen R t ≫ c (initialPolygonIndex k false) := by
  rw [← Category.assoc, rightBranchOpen_branchSwapIso,
    PolygonInfinitesimal.overlap, initialPolygonIndex_preceding]
  rfl

/-- Both oriented initial missing edges have exactly the same full image. -/
theorem initialPolygon_infinity_edge_range (b : Bool) :
    Set.range (rightBranchOpen R t ≫ O b ≫ c (initialPolygonIndex k b)) =
      Set.range (rightBranchOpen R t ≫ c (initialPolygonIndex k false)) := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, Category.id_comp]
  · simp only [↓reduceIte, initialPolygon_infinity_edge_true]
    have hs : Function.Surjective (edgeInversion R).hom :=
      (Scheme.homeoOfIso (edgeInversion R)).surjective
    change Set.range ((rightBranchOpen R t ≫ c (initialPolygonIndex k false)) ∘
      (edgeInversion R).hom) = _
    rw [Set.range_comp, hs.range_eq, Set.image_univ]

end FLT.Mazur.WeierstrassDividedDepth

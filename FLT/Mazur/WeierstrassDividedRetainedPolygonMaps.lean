/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingBranchSwapGeometry
public import FLT.Mazur.PolygonInfinitesimalFamily
public import FLT.Mazur.WeierstrassDividedRetainedPolygonLabels

/-!
# Explicit maps of both retained arms into the cyclic polygon

These maps use the original full node rings. Reversing the second arm's
coordinates makes both original consecutive edge equations commute.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonSmoothing
variable (R : Type*) [CommRing R] (t : R) [Fact (IsNilpotent t)] (k : ℕ)

/-- The specific full-chart comparison, with its original depth and Boolean label. -/
def retainedPolygonMap (a : Fin k) (opposite : Bool) :
    chart R t ⟶ PolygonInfinitesimal.scheme R t (2 * k + 3) (by omega) :=
  (if opposite then (branchSwapIso R t).hom else 𝟙 _) ≫
    PolygonInfinitesimal.chart R t (2 * k + 3) (by omega)
      (retainedPolygonIndex k a opposite)

instance retainedPolygonMap_isOpenImmersion (a : Fin k) (b : Bool) :
    IsOpenImmersion (retainedPolygonMap R t k a b) := by
  unfold retainedPolygonMap
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> infer_instance

/-- The comparison on the first arm uses the unmodified original node coordinates. -/
theorem retainedPolygonMap_false (a : Fin k) :
    retainedPolygonMap R t k a false =
      PolygonInfinitesimal.chart R t (2 * k + 3) (by omega)
        (retainedPolygonIndex k a false) := by
  simp only [retainedPolygonMap, Bool.false_eq_true, ↓reduceIte, Category.id_comp]

/-- Every original same-label consecutive edge commutes in the intended polygon. -/
@[reassoc] theorem retainedPolygonMap_adjacent (a : ℕ) (ha : a + 1 < k) (b : Bool) :
    leftBranchOpen R t ≫ retainedPolygonMap R t k ⟨a, by omega⟩ b =
      precedingBranch R t ≫ retainedPolygonMap R t k ⟨a + 1, ha⟩ b := by
  cases b
  · simp only [retainedPolygonMap_false]
    rw [PolygonInfinitesimal.overlap, retainedPolygonIndex_false_preceding]
  · simp only [retainedPolygonMap, ↓reduceIte, ← Category.assoc,
      leftBranchOpen_branchSwapIso_preceding, precedingBranch_branchSwapIso]
    have hi : (edgeInversion R).inv = (edgeInversion R).hom := rfl
    rw [hi, Category.assoc, Category.assoc]
    congr 1
    rw [PolygonInfinitesimal.overlap, retainedPolygonIndex_true_preceding]

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRetainedFixedBoundary
public import FLT.Mazur.WeierstrassDividedRetainedPolygonMaps

/-!
# Adjacent full retained maps into one normalized polygon

A single target smoothing and the recursively scaled full corrections give
compatible maps at both retained labels. No immersion property is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (π τ : R) [Fact (IsNilpotent τ)]
  (q : Rˣ) (hq : π * (q : R) = τ) (α : Rˣ) (k : ℕ)

/-- The entire node comparison at a prescribed depth and original retained label. -/
def retainedFixedPolygonMap (V : (ChartRing π)ˣ) (a : Fin k) (b : Bool) :
    PolygonSmoothing.chart R π ⟶ PolygonInfinitesimal.scheme R τ (2 * k + 3) (by omega) :=
  retainedFixedSmoothingChart π τ (q : R) hq
    (retainedScaledCorrectionUnit π (retainedDepthScale q α a.val) V) ≫
      retainedPolygonMap R τ k a b

/-- Equal full corrections on the source edge give equality in the same target polygon. -/
@[reassoc] theorem retainedFixedPolygonMap_adjacent (a : ℕ) (ha : a + 1 < k)
    (V V' : (ChartRing π)ˣ)
    (hV : Units.map (leftLaurentMap π).toMonoidHom V =
      Units.map (retainedPrecedingEvaluation π).toMonoidHom V') (b : Bool) :
    leftBranchOpen R π ≫ retainedFixedPolygonMap π τ q hq α k V ⟨a, by omega⟩ b =
      precedingBranch R π ≫ retainedFixedPolygonMap π τ q hq α k V' ⟨a + 1, ha⟩ b := by
  simp only [retainedFixedPolygonMap, ← Category.assoc]
  rw [retainedDepthScale_succ, retainedFixedSmoothingChart_outgoing,
    retainedFixedSmoothingChart_incoming π τ q hq (retainedDepthScale q α a) V V' hV]
  rw [Category.assoc, Category.assoc, retainedPolygonMap_adjacent R τ k a ha b]

end FLT.Mazur.WeierstrassDividedDepth

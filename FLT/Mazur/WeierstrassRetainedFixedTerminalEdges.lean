/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRetainedFixedPolygon
public import FLT.Mazur.WeierstrassRetainedDepthEdgeUnit

/-!
# Both last retained boundaries at terminal polygon label zero

Both arms use the reciprocal of the full outgoing unit. The false label
lands in the terminal right puncture and the true label in its left puncture.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (π τ : R) [Fact (IsNilpotent τ)]
  (q : Rˣ) (hq : π * (q : R) = τ) (α : Rˣ) (j : ℕ) (V : (ChartRing π)ˣ)
local notation "U" => retainedScaledCorrectionUnit π (retainedDepthScale q α j) V
local notation "u" => retainedFixedEdgeUnit π q U
local notation "B" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (LaurentUnitPoints.evalUnit (R := R) (u)⁻¹)))
local notation "P" => PolygonInfinitesimal.chart R τ (2 * (j + 1) + 3) (by omega) 0

/-- The last unmodified arm reaches the right puncture of terminal label zero. -/
@[reassoc] theorem retainedFixedPolygonMap_last_false :
    leftBranchOpen R π ≫
        retainedFixedPolygonMap π τ q hq α (j + 1) V ⟨j, by omega⟩ false =
      B ≫ rightBranchOpen R τ ≫ P := by
  rw [retainedFixedPolygonMap, ← Category.assoc, retainedFixedSmoothingChart_outgoing,
    Category.assoc, retainedPolygonMap_false, PolygonInfinitesimal.overlap,
    retainedPolygonIndex_false_terminal]
  rw [NodalFiber.unitParameter_inverse]
  simp only [precedingBranch, Category.assoc]

/-- The last reversed arm reaches the left puncture across the cyclic index boundary. -/
@[reassoc] theorem retainedFixedPolygonMap_last_true :
    leftBranchOpen R π ≫
        retainedFixedPolygonMap π τ q hq α (j + 1) V ⟨j, by omega⟩ true =
      B ≫ leftBranchOpen R τ ≫ P := by
  rw [retainedFixedPolygonMap, ← Category.assoc, retainedFixedSmoothingChart_outgoing,
    Category.assoc, retainedPolygonMap]
  simp only [↓reduceIte, ← Category.assoc, leftBranchOpen_branchSwapIso_preceding]
  have hi : (edgeInversion R).inv = (edgeInversion R).hom := rfl
  rw [hi, NodalFiber.unitParameter_inverse]
  simp only [Category.assoc]
  rw [PolygonInfinitesimal.overlap R τ _ _ 0, retainedPolygonIndex_true_terminal]

/-- The Boolean labels select the exact two terminal punctures with the same full unit. -/
@[reassoc] theorem retainedFixedPolygonMap_last (b : Bool) :
    leftBranchOpen R π ≫
        retainedFixedPolygonMap π τ q hq α (j + 1) V ⟨j, by omega⟩ b =
      B ≫ (if b then leftBranchOpen R τ else rightBranchOpen R τ) ≫ P := by
  cases b
  · exact retainedFixedPolygonMap_last_false π τ q hq α j V
  · exact retainedFixedPolygonMap_last_true π τ q hq α j V

end FLT.Mazur.WeierstrassDividedDepth

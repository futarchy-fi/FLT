/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineStructuralRelativeDimension
public import FLT.Mazur.PolygonCompleteNodeRelativeDimension

/-!
# Actual relative-curve opens near generic generizations of complete nodes

The affine rank calculation now yields an open subscheme of the original
complete family on which its original structural morphism has relative
dimension one. The affine chart is chosen from the existing scheme basis.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
attribute [local irreducible] originalStageToCompatibleProj

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)

/-- Each generic node generization has an actual open neighborhood of relative dimension one. -/
theorem completeNodeGenerization_exists_dimensionOpen (y : exactVeroneseProj K n h)
    (hy : y ⤳ completeNode K n h i)
    (ht : PowerSeries.X ∉ ((exactVeroneseProjToBase K n h) y).asIdeal) :
    ∃ V : (exactVeroneseProj K n h).Opens, y ∈ V ∧
      SmoothOfRelativeDimension 1 (V.ι ≫ exactVeroneseProjToBase K n h) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    (exactVeroneseProj K n h).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (completeNode K n h i)) isOpen_univ
  exact AffineStructuralRelativeDimension.exists_open (exactVeroneseProjToBase K n h)
    ⟨U, hU⟩ ⟨y, hy.mem_open U.isOpen hxU⟩ 1
    (completeNodeGenerization_point_relativeDimension K n h i ⟨U, hU⟩ hxU y hy ht)

end FLT.Mazur.PolygonInfinitesimalStages

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothDimension
/-!
# Dimension bounds from scheme open covers

Transport the dimension of each chart to its open range, then apply the
local dimension bound. Any chart also bounds the ambient dimension below.
-/

@[expose] public section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OpenCoverDimension
universe u
variable {X Y : Scheme.{u}}
/-- An upper bound on chart dimensions bounds the covered scheme. -/
theorem le (U : X.OpenCover) (d : WithBot ℕ∞)
    (h : ∀ i, topologicalKrullDim (U.X i) ≤ d) : topologicalKrullDim X ≤ d := by
  apply FCurve.topologicalKrullDim_le_of_open_cover d
  intro x
  obtain ⟨i, y, rfl⟩ := U.exists_eq x
  refine ⟨(U.f i).opensRange, ⟨y, rfl⟩, ?_⟩
  have he := (U.f i).isoOpensRange.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq
    (U.f i).isoOpensRange.hom
  exact he.symm.le.trans (h i)
/-- An open chart has no larger dimension than its ambient scheme. -/
theorem chart_le (f : Y ⟶ X) [IsOpenImmersion f] :
    topologicalKrullDim Y ≤ topologicalKrullDim X :=
  f.isOpenEmbedding.isInducing.topologicalKrullDim_le
end FLT.Mazur.OpenCoverDimension

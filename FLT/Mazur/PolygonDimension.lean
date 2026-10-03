/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonNodeDimension
public import FLT.Mazur.OpenCoverDimension
public import FLT.Mazur.PolygonCoconeComparison
public import FLT.Mazur.PolygonNormalizationFinite
/-!
# Dimension one for every polygon pinching cocone

The affine node charts have dimension one. The remaining one-gon torus
chart has dimension at most one because it embeds in the affine line.
Open covers and a node chart give both bounds on the polygon dimension.
-/

open CategoryTheory AlgebraicGeometry
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace FLT.Mazur.PolygonDimension
variable (K : Type u) [Field K]
/-- The split node chart has dimension one. -/
theorem node : topologicalKrullDim (PolygonNodeBranches.node K) = 1 := by
  exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).trans (PolygonNodeDimension.node K)
/-- The one-gon node chart has dimension one. -/
theorem oneGonChart :
    topologicalKrullDim (Spec (.of (PolygonNodePresentation.B (R := K)))) = 1 := by
  exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).trans (PolygonNodeDimension.oneGon K)
/-- The torus chart has dimension at most one. -/
theorem torus_le : topologicalKrullDim (ProjectiveLine.overlap K) ≤ 1 := by
  have h := OpenCoverDimension.chart_le (ProjectiveLine.overlapLeft K)
  have he : topologicalKrullDim (ProjectiveLine.chart K) = 1 :=
    (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).trans (PolygonNodeDimension.polynomial K)
  exact h.trans he.le
/-- The cyclic polygon has dimension one. -/
theorem cyclic (n : ℕ) (hn : 2 ≤ n) :
    topologicalKrullDim (PolygonCyclicAtlas.scheme K n hn) = 1 := by
  apply le_antisymm
  · apply OpenCoverDimension.le (PolygonCyclicNormalizationFinite.targetCover K n hn)
    intro i
    exact (node K).le
  · rw [← node K]
    exact OpenCoverDimension.chart_le (PolygonCyclicAtlas.chart K n hn ⟨0, by omega⟩)
/-- The one-gon has dimension one. -/
theorem oneGon : topologicalKrullDim (OneGonGluing.scheme K) = 1 := by
  apply le_antisymm
  · apply OpenCoverDimension.le (OneGonNormalizationFinite.targetCover K)
    intro i
    cases i
    · exact (oneGonChart K).le
    · exact torus_le K
  · rw [← oneGonChart K]
    exact OpenCoverDimension.chart_le (OneGonGluing.node K)
/-- The specified polygon has dimension one for every positive size. -/
theorem atlas (n : ℕ) [NeZero n] : topologicalKrullDim (PolygonAtlas.polygon K n).left = 1 := by
  rcases n with _ | (_ | n)
  · exact (NeZero.ne 0 rfl).elim
  · exact oneGon K
  · exact cyclic K (n + 2) (by omega)
open PolygonPinching CategoryTheory.Limits
variable (n : ℕ) [NeZero n] (hn : 0 < n) {C : Over (Spec (.of K))}
  (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
include h in
/-- Every supplied polygon cocone has dimension one. -/
theorem dimension : topologicalKrullDim C.left = 1 := by
  let e := (Over.forget (Spec (.of K))).mapIso (polygonIso K n hn p q h)
  exact (e.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq e.hom).symm.trans (atlas K n)
end FLT.Mazur.PolygonDimension

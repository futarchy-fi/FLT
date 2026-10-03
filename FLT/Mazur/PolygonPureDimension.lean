/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonComponentImages
public import FLT.Mazur.PolygonDimension
public import FLT.Mazur.CurveFiberHypotheses
public import FLT.Mazur.EtaleDimGe
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
/-!
# Pure dimension one of polygon pinching cocones

Every irreducible component contains a Laurent open of dimension one.
The dimension of the whole polygon bounds every component above.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped Polynomial LaurentPolynomial
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace FLT.Mazur.PolygonPureDimension
open PolygonPinching
variable (K : Type u) [Field K]
theorem torus_dimension : topologicalKrullDim (ProjectiveLine.overlap K) = 1 := by
  apply le_antisymm (PolygonDimension.torus_le K)
  change 1 ≤ topologicalKrullDim (PrimeSpectrum K[T;T⁻¹])
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  let : Module.Flat K[X] K[T;T⁻¹] :=
    IsLocalization.flat K[T;T⁻¹] (Submonoid.powers (Polynomial.X : K[X]))
  let : Algebra.FinitePresentation K[X] K[T;T⁻¹] :=
    IsLocalization.Away.finitePresentation (Polynomial.X : K[X])
  exact FCurve.oneLeRingKrullDimOfFlatPolynomial K K[T;T⁻¹]
variable (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
include h in
theorem component_dimension (i : Fin n) :
    topologicalKrullDim (Set.range (componentι K n i ≫ p).left) = 1 := by
  apply le_antisymm
  · exact (topologicalKrullDim_subspace_le _ _).trans
      (PolygonDimension.dimension K n hn p q h).le
  · rw [← torus_dimension K]
    have := torus_isOpenImmersion K n hn p q h i
    let f := (torusToComponent K ≫ componentι K n i ≫ p).left
    have hf (x : ProjectiveLine.overlap K) : f x ∈ Set.range (componentι K n i ≫ p).left := by
      refine ⟨(torusToComponent K).left x, ?_⟩
      exact (Scheme.Hom.comp_apply _ _ _).symm
    exact (f.isOpenEmbedding.isInducing.codRestrict hf).topologicalKrullDim_le
include h in
theorem pureDimension : FCurve.CurveFiberHypotheses.PureDimensionOne C.left := by
  intro Z hZ
  rw [PolygonComponentImages.components_eq K n hn p q h] at hZ
  obtain ⟨i, rfl⟩ := hZ
  exact component_dimension K n hn p q h i
end FLT.Mazur.PolygonPureDimension

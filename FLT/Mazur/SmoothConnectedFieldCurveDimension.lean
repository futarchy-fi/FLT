/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineStructuralStandardSmoothChart
public import FLT.Mazur.ConnectedJacobsonNoDiscreteOpen
public import FLT.Mazur.StandardSmoothFieldDimension
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Relative dimension of smooth connected field curves

A connected smooth scheme of topological dimension one over a field has
relative dimension one. Standard smooth charts have dimension at most one;
a zero dimensional chart would isolate a point in the connected Jacobson space.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.FCurve
set_option backward.isDefEq.respectTransparency false

/-- Smooth connected field curves have genuine relative dimension one. -/
theorem smooth_connected_fieldCurve_relativeDimension
    {K : Type} [Field K] {X : Scheme} [ConnectedSpace X]
    (f : X ⟶ Spec (.of K)) [Smooth f] (hX : topologicalKrullDim X = 1) :
    SmoothOfRelativeDimension 1 f := by
  let _ := LocallyOfFiniteType.jacobsonSpace f
  have hlocal : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧
      SmoothOfRelativeDimension 1 (V.ι ≫ f) := by
    intro x
    obtain ⟨A, a, j, hstd, hj, ⟨y, hy⟩, hjf⟩ :=
      AffineStructuralStandardSmoothChart.exists_chart f x
    let _ := hj
    let _ : Nontrivial A := y.nontrivial
    let _ := a.toAlgebra
    let _ : Algebra.IsStandardSmooth K A := RingHom.isStandardSmooth_algebraMap.mp hstd
    obtain ⟨d, hd, hdim⟩ := standardSmooth_exists_dimension K A
    let _ := hd
    have hle : (d : WithBot ℕ∞) ≤ 1 := by
      rw [← hdim, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
      exact j.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans_eq hX
    have hdne : d ≠ 0 := by
      intro hz
      let _ : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
      let _ : Ring.KrullDimLE 0 A := Ring.krullDimLE_iff.mpr (by simpa [hz] using hdim.le)
      let _ : IsArtinianRing A := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
      let _ : DiscreteTopology (Spec A) :=
        inferInstanceAs (DiscreteTopology (PrimeSpectrum A))
      let _ : Nonempty (Spec A) := ⟨y⟩
      exact not_openEmbedding_discrete_of_positive_dimension
        (by rw [hX]; exact zero_lt_one) j j.isOpenEmbedding
    have hdle : d ≤ 1 := by exact_mod_cast hle
    have hd1 : d = 1 := by omega
    subst d
    have hjd : SmoothOfRelativeDimension 1 (j ≫ f) := by
      rw [hjf, HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
      apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
      change RingHom.IsStandardSmoothOfRelativeDimension 1 (algebraMap K A)
      rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
      exact hd
    refine ⟨j.opensRange, ⟨y, hy⟩, ?_⟩
    rw [← IsOpenImmersion.isoOfRangeEq_inv_fac j (Scheme.Opens.ι j.opensRange)
      (congr_arg Opens.carrier j.opensRange.opensRange_ι.symm), Category.assoc,
      MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension 1)]
    exact hjd
  choose V hx hd using hlocal
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension 1) V
    (top_le_iff.mp fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hx x⟩) hd

end FLT.Mazur.FCurve

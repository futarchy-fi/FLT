/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SmoothConnectedFieldCurveDimension

/-!
# Relative dimension of smooth opens in connected field curves

The smooth open can be disconnected. Its charts embed openly in the original
connected dimension-one Jacobson curve, which rules out zero-dimensional charts.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.FCurve
set_option backward.isDefEq.respectTransparency false

/-- Every smooth open of a connected field curve has relative dimension one. -/
theorem smooth_open_fieldCurve_relativeDimension
    {K : Type} [Field K] {X Y : Scheme} [ConnectedSpace X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (j : Y ⟶ X) [IsOpenImmersion j] [Smooth (j ≫ f)]
    (hX : topologicalKrullDim X = 1) : SmoothOfRelativeDimension 1 (j ≫ f) := by
  let _ := LocallyOfFiniteType.jacobsonSpace f
  have hlocal : ∀ x : Y, ∃ V : Y.Opens, x ∈ V ∧
      SmoothOfRelativeDimension 1 (V.ι ≫ (j ≫ f)) := by
    intro x
    obtain ⟨A, a, k, hstd, hk, ⟨y, hy⟩, hkf⟩ :=
      AffineStructuralStandardSmoothChart.exists_chart (j ≫ f) x
    let _ := hk
    let _ : Nontrivial A := y.nontrivial
    let _ := a.toAlgebra
    let _ : Algebra.IsStandardSmooth K A := RingHom.isStandardSmooth_algebraMap.mp hstd
    obtain ⟨d, hd, hdim⟩ := standardSmooth_exists_dimension K A
    let _ := hd
    have hle : (d : WithBot ℕ∞) ≤ 1 := by
      rw [← hdim, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
      exact (k ≫ j).isOpenEmbedding.isInducing.topologicalKrullDim_le.trans_eq hX
    have hdne : d ≠ 0 := by
      intro hz
      let _ : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
      let _ : Ring.KrullDimLE 0 A := Ring.krullDimLE_iff.mpr (by simpa [hz] using hdim.le)
      let _ : IsArtinianRing A := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
      let _ : DiscreteTopology (Spec A) :=
        inferInstanceAs (DiscreteTopology (PrimeSpectrum A))
      let _ : Nonempty (Spec A) := ⟨y⟩
      exact not_openEmbedding_discrete_of_positive_dimension
        (by rw [hX]; exact zero_lt_one) (k ≫ j) (k ≫ j).isOpenEmbedding
    have hdle : d ≤ 1 := by exact_mod_cast hle
    have hd1 : d = 1 := by omega
    subst d
    have hkd : SmoothOfRelativeDimension 1 (k ≫ (j ≫ f)) := by
      rw [hkf, HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
      apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
      change RingHom.IsStandardSmoothOfRelativeDimension 1 (algebraMap K A)
      rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
      exact hd
    refine ⟨k.opensRange, ⟨y, hy⟩, ?_⟩
    rw [← IsOpenImmersion.isoOfRangeEq_inv_fac k (Scheme.Opens.ι k.opensRange)
      (congr_arg Opens.carrier k.opensRange.opensRange_ι.symm), Category.assoc,
      MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension 1)]
    exact hkd
  choose V hx hd using hlocal
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension 1) V
    (top_le_iff.mp fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hx x⟩) hd

end FLT.Mazur.FCurve

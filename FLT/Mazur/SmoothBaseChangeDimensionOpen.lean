/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineStructuralStandardSmoothChart
public import FLT.Mazur.CartesianStandardSmoothDimension
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Dimension neighborhoods detected by an actual smooth fiber

Near any point of a cartesian relative-dimension-d fiber, a smooth total
family has an actual open neighborhood of relative dimension d.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.SmoothBaseChangeDimensionOpen

set_option backward.isDefEq.respectTransparency false

/-- A relative smooth fiber determines the total family's dimension near each of its points. -/
theorem exists_open {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    {X Y : Scheme} (f : X ⟶ Spec (.of R)) (g : Y ⟶ Spec (.of S)) (i : Y ⟶ X)
    (h : IsPullback i g f (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    [Smooth f] (d : ℕ) [SmoothOfRelativeDimension d g] (y : Y) :
    ∃ V : X.Opens, i y ∈ V ∧ SmoothOfRelativeDimension d (V.ι ≫ f) := by
  obtain ⟨A, a, j, hstd, hj, hy, hjf⟩ :=
    AffineStructuralStandardSmoothChart.exists_chart f (i y)
  let _ := a.toAlgebra
  let _ : Algebra.IsStandardSmooth R A := RingHom.isStandardSmooth_algebraMap.mp hstd
  let _ := hj
  let _ : IsAffineHom i := MorphismProperty.of_isPullback h.flip inferInstance
  let k := pullback.fst j i
  let g' := pullback.snd j i ≫ g
  have hP : IsPullback k g' (Spec.map (CommRingCat.ofHom a))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
    rw [← hjf]
    exact (IsPullback.of_hasPullback j i).paste_vert h
  let _ : SmoothOfRelativeDimension d g' :=
    IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension d)
      inferInstance (pullback.snd j i)
  obtain ⟨z, hz⟩ := hy
  obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := j) (g := i) z y hz
  have hd := CartesianStandardSmoothDimension.of_isPullback R S A k g' hP d w
  have hdj : SmoothOfRelativeDimension d (j ≫ f) := by
    rw [hjf, HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension d)]
    apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
    change RingHom.IsStandardSmoothOfRelativeDimension d (algebraMap R A)
    rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    exact hd
  refine ⟨j.opensRange, ⟨z, hz⟩, ?_⟩
  rw [← IsOpenImmersion.isoOfRangeEq_inv_fac j (Scheme.Opens.ι j.opensRange)
    (congr_arg TopologicalSpace.Opens.carrier j.opensRange.opensRange_ι.symm), Category.assoc,
    MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension d)]
  exact hdj

/-- The same conclusion holds at a smooth point, using only the smooth part of the fiber. -/
theorem exists_open_at_smoothPoint {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    {X Y : Scheme} (f : X ⟶ Spec (.of R)) (g : Y ⟶ Spec (.of S)) (i : Y ⟶ X)
    (h : IsPullback i g f (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    [LocallyOfFinitePresentation f] (d : ℕ)
    [SmoothOfRelativeDimension d ((i ⁻¹ᵁ f.smoothLocus).ι ≫ g)]
    (y : Y) (hy : i y ∈ f.smoothLocus) :
    ∃ V : X.Opens, i y ∈ V ∧ SmoothOfRelativeDimension d (V.ι ≫ f) := by
  let W := f.smoothLocus
  let _ : Smooth (W.ι ≫ f) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    exact W.ι_preimage_self
  have hp := (isPullback_morphismRestrict i W).paste_vert h
  obtain ⟨V, hyV, hd⟩ := exists_open (W.ι ≫ f) ((i ⁻¹ᵁ W).ι ≫ g)
    (i ∣_ W) hp d ⟨y, hy⟩
  let j : V.toScheme ⟶ X := V.ι ≫ W.ι
  have hdj : SmoothOfRelativeDimension d (j ≫ f) := by
    simpa only [j, Category.assoc] using hd
  have hyj : i y ∈ j.opensRange := by
    refine ⟨⟨(i ∣_ W) ⟨y, hy⟩, hyV⟩, ?_⟩
    change W.ι ((i ∣_ W) ⟨y, hy⟩) = i y
    exact congrArg (fun k ↦ k ⟨y, hy⟩) (morphismRestrict_ι i W)
  refine ⟨j.opensRange, hyj, ?_⟩
  rw [← IsOpenImmersion.isoOfRangeEq_inv_fac j (Scheme.Opens.ι j.opensRange)
    (congr_arg TopologicalSpace.Opens.carrier j.opensRange.opensRange_ι.symm), Category.assoc,
    MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension d)]
  exact hdj

end FLT.Mazur.SmoothBaseChangeDimensionOpen

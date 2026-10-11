/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineStructuralSmoothLocus
public import FLT.Mazur.PrimeCotangentSmoothDimension

/-!
# Actual relative-dimension neighborhoods from affine principal charts

A principal localization of the original structural coefficient map gives an
open neighborhood in the original scheme, with the same relative dimension.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.AffineStructuralRelativeDimension

set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))
  (U : X.affineOpens)

/-- A principal affine relative-dimension witness produces an actual open neighborhood. -/
theorem exists_open (x : U.1) (d : ℕ)
    (h : let _ := (AffineStructuralSmoothLocus.scalars f U).toAlgebra
      ∃ s : Γ(X, U), s ∉ (U.2.primeIdealOf x).asIdeal ∧
        Algebra.IsStandardSmoothOfRelativeDimension d R (Localization.Away s)) :
    ∃ V : X.Opens, x.val ∈ V ∧ SmoothOfRelativeDimension d (V.ι ≫ f) := by
  let A := Γ(X, U)
  let _ := (AffineStructuralSmoothLocus.scalars f U).toAlgebra
  obtain ⟨s, hs, hd⟩ := h
  let L := Localization.Away s
  let j : Spec (.of L) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ U.2.fromSpec
  have hj : IsOpenImmersion j := inferInstance
  have hdj : SmoothOfRelativeDimension d (j ≫ f) := by
    dsimp only [j]
    rw [Category.assoc, AffineStructuralSmoothLocus.fromSpec_toBase, ← Spec.map_comp]
    change SmoothOfRelativeDimension d (Spec.map (CommRingCat.ofHom (algebraMap R L)))
    rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension d)]
    apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
    change RingHom.IsStandardSmoothOfRelativeDimension d (algebraMap R L)
    rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    exact hd
  have hx : x.val ∈ j.opensRange := by
    have hs' : U.2.primeIdealOf x ∈
        Set.range (PrimeSpectrum.comap (algebraMap A L)) := by
      rw [PrimeSpectrum.localization_away_comap_range L s]
      exact hs
    obtain ⟨z, hz⟩ := hs'
    refine ⟨z, ?_⟩
    change U.2.fromSpec (PrimeSpectrum.comap (algebraMap A L) z) = x.val
    rw [hz, U.2.fromSpec_primeIdealOf]
  refine ⟨j.opensRange, hx, ?_⟩
  rw [← IsOpenImmersion.isoOfRangeEq_inv_fac j (Scheme.Opens.ι j.opensRange)
    (congr_arg TopologicalSpace.Opens.carrier j.opensRange.opensRange_ι.symm), Category.assoc,
    MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension d)]
  exact hdj

end FLT.Mazur.AffineStructuralRelativeDimension

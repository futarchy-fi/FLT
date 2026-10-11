/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineStructuralSmoothLocus
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree

/-!
# Standard-smooth charts over the original affine base

Every point of a smooth scheme over an affine base lies in a standard-smooth
chart over that same coefficient ring, with its original structure map.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.AffineStructuralStandardSmoothChart

set_option backward.isDefEq.respectTransparency false

/-- A smooth point admits a standard-smooth affine chart over the unchanged base ring. -/
theorem exists_chart {R : Type} [CommRing R] {X : Scheme}
    (f : X ⟶ Spec (.of R)) [Smooth f] (x : X) :
    ∃ (A : CommRingCat) (a : R →+* A) (j : Spec A ⟶ X),
      a.IsStandardSmooth ∧ IsOpenImmersion j ∧ x ∈ Set.range j ∧
        j ≫ f = Spec.map (CommRingCat.ofHom a) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let U : X.affineOpens := ⟨V, hV⟩
  let A := Γ(X, U)
  let _ := (AffineStructuralSmoothLocus.scalars f U).toAlgebra
  have hs : Smooth (U.2.fromSpec ≫ f) := inferInstance
  rw [AffineStructuralSmoothLocus.fromSpec_toBase,
    HasRingHomProperty.Spec_iff (P := @Smooth)] at hs
  let _ : Algebra.Smooth R A := RingHom.smooth_algebraMap.mp hs
  let p := (U.2.primeIdealOf ⟨x, hxV⟩).asIdeal
  obtain ⟨s, hs, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth R p
  let L := Localization.Away s
  let _ := hstd
  let j : Spec (.of L) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap A L)) ≫ U.2.fromSpec
  refine ⟨.of L, algebraMap R L, j,
    RingHom.isStandardSmooth_algebraMap.mpr hstd, inferInstance, ?_, ?_⟩
  · have hp : U.2.primeIdealOf ⟨x, hxV⟩ ∈
        Set.range (PrimeSpectrum.comap (algebraMap A L)) := by
      rw [PrimeSpectrum.localization_away_comap_range L s]
      exact hs
    obtain ⟨z, hz⟩ := hp
    refine ⟨z, ?_⟩
    change U.2.fromSpec (PrimeSpectrum.comap (algebraMap A L) z) = x
    rw [hz, U.2.fromSpec_primeIdealOf]
  · dsimp only [j]
    rw [Category.assoc, AffineStructuralSmoothLocus.fromSpec_toBase, ← Spec.map_comp]
    rfl

end FLT.Mazur.AffineStructuralStandardSmoothChart

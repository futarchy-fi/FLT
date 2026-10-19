/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarAlgebraicClosureTests
public import FLT.Mazur.AffineBoundaryIntegralFlatCriterion

/-!
# Constructing exact boundary fibers from canonical geometric tests

The scalar prime stays in the original boundary ring. Its contraction chooses
one algebraic closure in which values of the original invariant coordinates
detect the entire boundary fiber. Full branch integrality is still required
to promote these exact-fiber equations to a scalar neighborhood.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.AffineScalarBoundaryNilpotence
open ScalarTestLocalization
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R B T : Type} [CommRing R] [CommRing B] [CommRing T]
  (s : R →+* B) (κ : R →+* T)

/-- Canonical geometric tests detect every point of the entire exact original boundary fiber. -/
theorem boundary_exact_fiber_iff_residue_tests (hs : s.FiniteType)
    (a : Finset B) (P : PrimeSpectrum T) :
    (∀ z : boundaryProduct s κ, boundaryScalarProjection s κ z = P →
      ∀ t ∈ a, t ∈ (boundaryProjection s κ z).asIdeal) ↔
      ∀ t ∈ a, residueGeometricTest s (PrimeSpectrum.comap κ P) t := by
  constructor
  · intro h t ht
    apply (residueGeometricTest_iff_original_fiber s _ hs t).mpr
    intro q hq
    obtain ⟨z, hz, hp⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := Spec.map (CommRingCat.ofHom s)) (g := Spec.map (CommRingCat.ofHom κ)) q P hq
    change boundaryProjection s κ z = q at hz
    change boundaryScalarProjection s κ z = P at hp
    simpa only [hz] using h z hp t ht
  · intro h z hz t ht
    apply (residueGeometricTest_iff_original_fiber s _ hs t).mp (h t ht)
    have hc := congrArg (fun f ↦ f z) (pullback.condition
      (f := Spec.map (CommRingCat.ofHom s)) (g := Spec.map (CommRingCat.ofHom κ)))
    change PrimeSpectrum.comap s (boundaryProjection s κ z) =
      PrimeSpectrum.comap κ (boundaryScalarProjection s κ z) at hc
    rwa [hz] at hc

attribute [local irreducible] boundaryCoordinate

/-- Geometric values and full integral flat branches construct an original scalar neighborhood. -/
theorem boundaryScalar_mem_of_geometric_integral_tests (hs : s.FiniteType)
    (S : Type) [CommRing S] [Algebra T S] [Module.Flat T S]
    (a : Finset B) (Q : PrimeSpectrum S)
    (hi : ∀ t ∈ a, boundaryIntegralFlatTest s κ S Q t)
    (hg : ∀ t ∈ a, residueGeometricTest s
      (PrimeSpectrum.comap κ (PrimeSpectrum.comap (algebraMap T S) Q)) t) :
    PrimeSpectrum.comap (algebraMap T S) Q ∈ boundaryScalarNilpotenceOpen s κ a :=
  boundaryScalar_mem_of_integral_criterion s κ S a Q hi
    ((boundary_exact_fiber_iff_residue_tests s κ hs a _).mpr hg)

/-- A failed exact boundary test produces a geometric character at the unchanged scalar center. -/
theorem exists_boundary_residue_failure (hs : s.FiniteType) (P : PrimeSpectrum T)
    (z : boundaryProduct s κ) (hz : boundaryScalarProjection s κ z = P)
    (t : B) (ht : t ∉ (boundaryProjection s κ z).asIdeal) :
    ∃ v : B →+* AlgebraicClosure (PrimeSpectrum.comap κ P).asIdeal.ResidueField,
      v.comp s = algebraMap R _ ∧ v t ≠ 0 := by
  apply exists_residue_geometric_failure s _ hs t (boundaryProjection s κ z) _ ht
  have hc := congrArg (fun f ↦ f z) (pullback.condition
    (f := Spec.map (CommRingCat.ofHom s)) (g := Spec.map (CommRingCat.ofHom κ)))
  change PrimeSpectrum.comap s (boundaryProjection s κ z) =
    PrimeSpectrum.comap κ (boundaryScalarProjection s κ z) at hc
  rwa [hz] at hc

end FLT.Mazur.AffineScalarBoundaryNilpotence

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TranscendentalCoefficientOrbitAvoidance
public import FLT.Mazur.ExtendedAffineRationalDensity

/-!
# Algebraic point orbits inside opens with transcendental coefficients

A finite family of nonempty opens on the extended integral affine fiber
contains one entire residue-field conjugacy orbit of algebraic rational points.
The opens are unchanged and may have infinite coefficient-automorphism orbit.
This is an affine coefficient reduction, not yet original étale-test assembly.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.TranscendentalCoefficientOrbitAvoidance
open scoped TensorProduct
open TensorCoefficientDetection AlgebraicTensorCoefficientOrbit
variable {k L K A J : Type*} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra L K] [Algebra.IsAlgebraic k L] [IsAlgClosed L]
  [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
  [IsDomain (L ⊗[k] A)] [Finite J]

/-- All conjugates of one algebraic rational point lie in every original extended open. -/
theorem exists_point_orbit_in_opens
    (U : J → TopologicalSpace.Opens (PrimeSpectrum (K ⊗[L] (L ⊗[k] A))))
    (hU : ∀ j, (U j : Set (PrimeSpectrum (K ⊗[L] (L ⊗[k] A)))).Nonempty) :
    ∃ p : L ⊗[k] A →ₐ[L] L, ∀ (σ : L ≃ₐ[k] L) (j : J),
      extendedPoint (K := K) (conjugatePoint p σ) ∈ U j := by
  classical
  have hb (j : J) : ∃ x : K ⊗[L] (L ⊗[k] A), x ≠ 0 ∧
      PrimeSpectrum.basicOpen x ≤ U j := by
    obtain ⟨v, ⟨x, rfl⟩, hv, hsub⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_nonempty_subset (hU j) (U j).isOpen
    refine ⟨x, ?_, hsub⟩
    rintro rfl
    simp only [PrimeSpectrum.basicOpen_zero, TopologicalSpace.Opens.coe_bot,
      Set.not_nonempty_empty] at hv
  choose x hx hsub using hb
  obtain ⟨p, hp⟩ := exists_point_all_conjugates x hx
  exact ⟨p, fun σ j ↦ hsub j (hp σ j)⟩

/-- The single-open form retains membership for the actual transcendental condition. -/
theorem exists_point_orbit_in_open
    (U : TopologicalSpace.Opens (PrimeSpectrum (K ⊗[L] (L ⊗[k] A))))
    (hU : (U : Set (PrimeSpectrum (K ⊗[L] (L ⊗[k] A)))).Nonempty) :
    ∃ p : L ⊗[k] A →ₐ[L] L, ∀ σ : L ≃ₐ[k] L,
      extendedPoint (K := K) (conjugatePoint p σ) ∈ U := by
  obtain ⟨p, hp⟩ := exists_point_orbit_in_opens (fun _ : Unit ↦ U) (fun _ ↦ hU)
  exact ⟨p, fun σ ↦ hp σ ()⟩

end FLT.Mazur.TranscendentalCoefficientOrbitAvoidance

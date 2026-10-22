/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeScalarPrincipalNeighborhood
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Exact scalar kernels on compact nonaffine schemes

The scalar image closure of a compact scheme is computed by the radical
of its global scalar kernel. Compactness supplies a uniform nilpotence
exponent; affineness and reducedness are unnecessary.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {X : Scheme.{0}} [CompactSpace X]
  (s : R →+* Γ(X, ⊤))

/-- Vanishing at every scalar image point detects a nilpotent full section. -/
theorem mem_scalarImage_vanishingIdeal_iff (r : R) :
    r ∈ PrimeSpectrum.vanishingIdeal (Set.range (scalarMorphism s)) ↔
      IsNilpotent (s r) := by
  rw [PrimeSpectrum.mem_vanishingIdeal, Scheme.isNilpotent_iff_basicOpen_eq_bot]
  constructor
  · intro h
    apply eq_bot_iff.mpr
    intro x hx
    have hx' : scalarMorphism s x ∈ PrimeSpectrum.basicOpen r := by
      change x ∈ scalarMorphism s ⁻¹ᵁ PrimeSpectrum.basicOpen r
      rwa [scalarMorphism_preimage]
    exact hx' (h _ ⟨x, rfl⟩)
  · intro h P hP
    obtain ⟨x, rfl⟩ := hP
    by_contra hx
    have hx' : x ∈ X.basicOpen (s r) := by
      rw [← scalarMorphism_preimage]
      exact hx
    rw [h] at hx'
    exact hx'

/-- The full coefficient kernel computes the closed scalar image, including accumulation. -/
theorem scalarImage_vanishingIdeal_eq_kernel_radical :
    PrimeSpectrum.vanishingIdeal (Set.range (scalarMorphism s)) =
      (RingHom.ker s).radical := by
  ext r
  rw [mem_scalarImage_vanishingIdeal_iff]
  change (∃ n : ℕ, s r ^ n = 0) ↔ ∃ n : ℕ, s (r ^ n) = 0
  simp only [map_pow]

/-- Closing a compact scalar image keeps its exact kernel equations. -/
theorem scalarImage_closure_eq_kernel_zeroLocus :
    closure (Set.range (scalarMorphism s)) =
      PrimeSpectrum.zeroLocus (RingHom.ker s : Set R) := by
  rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
    scalarImage_vanishingIdeal_eq_kernel_radical, PrimeSpectrum.zeroLocus_radical]

end FLT.Mazur.SchemeScalarPrincipalNeighborhood

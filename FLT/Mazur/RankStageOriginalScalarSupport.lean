/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeScalarPrincipalNeighborhood
public import FLT.Mazur.RelativeRankStratumThickenings
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Whole original scalar loci and pulled coefficient ideals

Containment of the full geometric scalar locus implies the exact spectrum
support needed for adic comparison. All primes over the scalar ideal are tested,
including primes whose scalar contraction strictly contains that ideal.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeScalarPulledIdealSupport
open SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {T X : Scheme} [IsAffine T]
  (σ : R →+* Γ(T, ⊤)) (J : Ideal R) (I : T.IdealSheafData)

omit [IsAffine T] in
/-- The full geometric scalar zero locus is precisely the coefficient zero locus. -/
theorem mem_scalar_zeroLocus_iff (x : T) :
    scalarMorphism σ x ∈ PrimeSpectrum.zeroLocus (J : Set R) ↔
      x ∈ T.zeroLocus (J.map σ : Set Γ(T, ⊤)) := by
  rw [← T.toSpecΓ_preimage_zeroLocus]
  change J ≤ Ideal.comap σ (T.toSpecΓ x).asIdeal ↔ J.map σ ≤ (T.toSpecΓ x).asIdeal
  exact Ideal.map_le_iff_le_comap.symm

/-- The whole geometric test yields support in the actual affine coefficient spectrum. -/
theorem scalar_support_of_geometric
    (h : ∀ x : T, scalarMorphism σ x ∈ PrimeSpectrum.zeroLocus (J : Set R) →
      x ∈ I.support) :
    PrimeSpectrum.zeroLocus (J.map σ : Set Γ(T, ⊤)) ⊆
      PrimeSpectrum.zeroLocus (I.ideal ⟨⊤, isAffineOpen_top T⟩ : Set Γ(T, ⊤)) := by
  rw [← T.toSpecΓ_image_zeroLocus, ← T.toSpecΓ_image_zeroLocus]
  apply Set.image_mono
  intro x hx
  apply (Scheme.IdealSheafData.mem_support_iff_of_mem
    (I := I) (U := ⟨⊤, isAffineOpen_top T⟩) (x := x) trivial).mp
  exact h x ((mem_scalar_zeroLocus_iff σ J x).mpr hx)

/-- A full scalar-locus test on the unchanged source controls the exact pulled ideal. -/
theorem pulled_scalar_support (K : X.IdealSheafData) (g : T ⟶ X)
    (h : ∀ x : T, scalarMorphism σ x ∈ PrimeSpectrum.zeroLocus (J : Set R) →
      g x ∈ K.support) :
    PrimeSpectrum.zeroLocus (J.map σ : Set Γ(T, ⊤)) ⊆
      PrimeSpectrum.zeroLocus ((K.comap g).ideal ⟨⊤, isAffineOpen_top T⟩ :
        Set Γ(T, ⊤)) := by
  apply scalar_support_of_geometric σ J (K.comap g)
  intro x hx
  rw [Scheme.IdealSheafData.support_comap]
  exact h x hx

end FLT.Mazur.SchemeScalarPulledIdealSupport

namespace FLT.Mazur.RelativeOrderedTuples
open SchemeScalarPrincipalNeighborhood SchemeScalarPulledIdealSupport
variable {S T : Scheme.{0}} [IsAffine T] (E : Over S)
  [Etale E.hom] [IsSeparated E.hom] (n : ℕ)
  {R : Type} [CommRing R] (σ : R →+* Γ(T, ⊤)) (J : Ideal R)
  (g : T ⟶ (rankImageOpen E n).toScheme)

/-- Whole original scalar-locus rank tests control the fixed original coordinate ideal. -/
theorem rankStage_original_scalar_support
    (h : ∀ x : T, scalarMorphism σ x ∈ PrimeSpectrum.zeroLocus (J : Set R) →
      (g ≫ (rankImageOpen E n).ι) x ∈ exactRank E n) :
    PrimeSpectrum.zeroLocus (J.map σ : Set Γ(T, ⊤)) ⊆
      PrimeSpectrum.zeroLocus
        (((rankStratumIdeal E n).comap g).ideal ⟨⊤, isAffineOpen_top T⟩ : Set Γ(T, ⊤)) := by
  apply pulled_scalar_support σ J (rankStratumIdeal E n) g
  intro x hx
  change (rankImageOpen E n).ι (g x) ∈ rankAtMost E n
  exact (h x hx).2

end FLT.Mazur.RelativeOrderedTuples

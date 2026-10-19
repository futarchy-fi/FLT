/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarMinimalCharacterNeighborhood
public import FLT.Mazur.AffineBoundaryTestKernels

/-!
# Original boundary neighborhoods from minimal scalar characters

Going down in the invariant scalar algebra propagates generic character
vanishing to every component of the full original boundary localization.
The constructed boundary scalar kills a whole test-ideal power and lies in
every full principal test-chart kernel. No boundary flatness is required.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.AffineScalarBoundaryNilpotence
open ScalarTestLocalization
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] boundaryProduct boundaryCoordinate
variable {R B T : Type} [CommRing R] [CommRing B] [CommRing T]
  (s : R →+* B) (κ : R →+* T) (a : Finset B) (P : PrimeSpectrum T)

/-- Generic scalar geometry supplies nilpotence on the full original boundary localization. -/
theorem boundaryScalar_mem_of_minimal_characters
    (hs : s.FiniteType) (hg : GeneralizingMap (PrimeSpectrum.comap s))
    (ha : ∀ Q : PrimeSpectrum R, Q.asIdeal ∈ minimalPrimes R →
      Q ≤ PrimeSpectrum.comap κ P →
      ∀ χ : B →+* AlgebraicClosure Q.asIdeal.ResidueField,
        χ.comp s = algebraMap R _ → ∀ t ∈ a, χ t = 0) :
    P ∈ boundaryScalarNilpotenceOpen s κ a := by
  apply (mem_boundaryScalarNilpotenceOpen_iff_components s κ a P).mpr
  intro q hq
  let z := boundaryComponentPoint s κ q
  have he : boundaryProjection s κ ≫ Spec.map (CommRingCat.ofHom s) =
      boundaryScalarProjection s κ ≫ Spec.map (CommRingCat.ofHom κ) := by
    unfold boundaryProjection boundaryScalarProjection boundaryProduct
    exact pullback.condition (f := Spec.map (CommRingCat.ofHom s))
      (g := Spec.map (CommRingCat.ofHom κ))
  have hc : PrimeSpectrum.comap s (boundaryProjection s κ z) =
      PrimeSpectrum.comap κ (boundaryScalarProjection s κ z) :=
    congrArg (fun f : boundaryProduct s κ ⟶ Spec (.of R) ↦ f z) he
  have hle : PrimeSpectrum.comap s (boundaryProjection s κ z) ≤
      PrimeSpectrum.comap κ P := by
    rw [hc]
    exact Ideal.comap_mono hq
  have hJ : Ideal.span (a : Set B) ≤ (boundaryProjection s κ z).asIdeal := by
    apply ideal_le_prime_of_minimal_scalar_characters s (PrimeSpectrum.comap κ P)
      (Ideal.span (a : Set B)) hs hg _ _ hle
    intro Q hQ hQP χ hχ
    exact Ideal.span_le.mpr (fun t ht ↦ ha Q hQ hQP χ hχ t ht)
  change Ideal.span _ ≤ q.val
  apply Ideal.span_le.mpr
  rintro _ ⟨t, ht, rfl⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  exact (boundaryComponent_equation_iff s κ q t).mpr (hJ (Ideal.subset_span ht))

/-- Construct one unchanged boundary scalar, a whole-power equation and every chart equation. -/
theorem boundary_scalar_equations_of_minimal_characters
    (hs : s.FiniteType) (hg : GeneralizingMap (PrimeSpectrum.comap s))
    (ha : ∀ Q : PrimeSpectrum R, Q.asIdeal ∈ minimalPrimes R →
      Q ≤ PrimeSpectrum.comap κ P →
      ∀ χ : B →+* AlgebraicClosure Q.asIdeal.ResidueField,
        χ.comp s = algebraMap R _ → ∀ t ∈ a, χ t = 0) :
    ∃ (order : ℕ) (r : T), r ∉ P.asIdeal ∧
      boundaryScalarHom s κ r ∈ ((boundaryTestIdeal s κ a) ^ order).annihilator ∧
      ∀ t ∈ a, r ∈ boundaryTestKernel s κ t := by
  obtain ⟨order, r, hr, he⟩ := (mem_boundaryScalarNilpotenceOpen s κ a P).mp
    (boundaryScalar_mem_of_minimal_characters s κ a P hs hg ha)
  exact ⟨order, r, hr, he,
    (boundary_power_annihilator_iff_testKernels s κ a r).mp ⟨order, he⟩⟩

end FLT.Mazur.AffineScalarBoundaryNilpotence

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityFourLawAffine

/-!
# The actual infinity outputs agree on the five-coordinate localization

The denominator is the product of the Z coordinates of the three inputs and
both intermediate sums. The four genuine laws specialize together, so the
five-affine theorem applies to their spectra without an affineness hypothesis
on the original full-cover member. No regularity of this denominator is claimed.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

attribute [local instance] infinityTripleFullSectionAlgebra

/-- The five actual input coordinates whose inversion permits affine associativity. -/
def infinityTripleAffineDenominator : Γ(InfinityTripleFull W hΔ, ⊤) :=
  ∏ i : Fin 5, infinityTripleScalarZ W hΔ (i.castAdd 2)

/-- A specialization with those five units identifies the actual two outer chart maps. -/
theorem infinityTriple_outputs_eq_after_units {S : Type u} [CommRing S] [Algebra R S]
    (f : Γ(InfinityTripleFull W hΔ, ⊤) →ₐ[R] S)
    (hu : ∀ i : Fin 5, IsUnit (f (infinityTripleScalarZ W hΔ (i.castAdd 2)))) :
    f.comp (infinityTripleScalarPoint W hΔ 5) =
      f.comp (infinityTripleScalarPoint W hΔ 6) := by
  apply infinityFourLaw_algHom_eq_of_units W hΔ
    (fun i => f.comp (infinityTripleScalarPoint W hΔ i))
    (fun j => f.comp (infinityTripleScalarLaw W hΔ j))
  · intro j
    rw [AlgHom.comp_assoc, infinityTripleScalarLaw_left]
  · intro j
    rw [AlgHom.comp_assoc, infinityTripleScalarLaw_right]
  · intro j
    rw [AlgHom.comp_assoc, infinityTripleScalarLaw_output]
  · exact hu

/-- Every input coordinate is a unit after inverting the single five-coordinate product. -/
theorem infinityTripleAffineDenominator_coordinate_unit (i : Fin 5) :
    IsUnit (algebraMap Γ(InfinityTripleFull W hΔ, ⊤)
      (Localization.Away (infinityTripleAffineDenominator W hΔ))
        (infinityTripleScalarZ W hΔ (i.castAdd 2))) := by
  apply isUnit_of_dvd_unit
    (map_dvd (algebraMap _ _) (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)))
  exact IsLocalization.Away.algebraMap_isUnit (infinityTripleAffineDenominator W hΔ)

/-- The actual normalized output maps agree in this explicitly constructed localization. -/
theorem infinityTriple_outputs_eq_localized :
    let f := IsScalarTower.toAlgHom R Γ(InfinityTripleFull W hΔ, ⊤)
      (Localization.Away (infinityTripleAffineDenominator W hΔ))
    f.comp (infinityTripleScalarPoint W hΔ 5) =
      f.comp (infinityTripleScalarPoint W hΔ 6) :=
  infinityTriple_outputs_eq_after_units W hΔ _
    (infinityTripleAffineDenominator_coordinate_unit W hΔ)

/-- Clearing localization gives an actual power annihilating each output section difference. -/
theorem infinityTriple_output_difference_torsion (a : Coordinate W 1) :
    ∃ n : ℕ, infinityTripleAffineDenominator W hΔ ^ n *
      (infinityTripleScalarPoint W hΔ 5 a - infinityTripleScalarPoint W hΔ 6 a) = 0 := by
  have h := DFunLike.congr_fun (infinityTriple_outputs_eq_localized W hΔ) a
  obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq
    (infinityTripleAffineDenominator W hΔ) h
  change infinityTripleAffineDenominator W hΔ ^ n *
    infinityTripleScalarPoint W hΔ 5 a =
    infinityTripleAffineDenominator W hΔ ^ n * infinityTripleScalarPoint W hΔ 6 a at hn
  exact ⟨n, by rw [mul_sub, hn, sub_self]⟩

end FLT.Mazur.WeierstrassIntegralChart

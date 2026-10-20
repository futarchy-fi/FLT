/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonFiniteCoefficientRecovery
public import FLT.Mazur.WeierstrassChartCoefficientSurjectivity

/-!
# Polynomial witnesses survive finite coefficient descent

Including the coefficients of a polynomial preimage makes that preimage
available in the model. Injective recovery then proves the original exact
character equation already over the finite coefficient ring.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.OneGonFiniteCoefficientCoordinates

open WeierstrassIntegralChart OneGonSmoothing MvPolynomial

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R G : Type*} [CommRing R] [AddCommMonoid G]
  (t : R) (j : Fin 3) (φ : Coordinate (equation t) j →ₐ[R] AddMonoidAlgebra R G)
  (s : Set R)

/-- The chart inclusion retains the full polynomial quotient. -/
theorem modelChartMap_mk (p : MvPolynomial (Fin 3) (modelRing t j φ s)) :
    modelChartMap t j φ s (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (map (modelRing t j φ s).val.toRingHom p) := by
  have h : (modelChartMap t j φ s).comp
      (Ideal.Quotient.mk (relations (equation (modelParameter t j φ s)) j)) =
        (Ideal.Quotient.mk (relations (equation t) j)).comp
          (map (modelRing t j φ s).val.toRingHom) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, map_C]
      simp only [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]
      change modelChartMap t j φ s (algebraMap _ _ a) = algebraMap R _ (a : R)
      exact modelChartMap_scalar t j φ s a
    · intro i
      simpa only [RingHom.comp_apply, map_X, coord] using modelChartMap_coord t j φ s i
  exact RingHom.congr_fun h p

/-- A polynomial whose coefficients were requested lifts to the exact model ring. -/
theorem exists_modelPolynomial (p : MvPolynomial (Fin 3) R)
    (hp : (p.coeffs : Set R) ⊆ s) :
    ∃ q : MvPolynomial (Fin 3) (modelRing t j φ s),
      map (modelRing t j φ s).val.toRingHom q = p := by
  apply mem_range_map_iff_coeffs_subset.mpr
  intro a ha
  exact ⟨⟨a, CharacterFiniteCoefficientModel.subset_coefficientRing _ _
    (Or.inl (hp ha))⟩, rfl⟩

/-- A specified full polynomial preimage of a character remains a preimage in the model. -/
theorem modelCoordinates_character_mem_range (g : G) (p : MvPolynomial (Fin 3) R)
    (hp : (p.coeffs : Set R) ⊆ s)
    (he : φ (Ideal.Quotient.mk _ p) = AddMonoidAlgebra.single g 1) :
    AddMonoidAlgebra.single g (1 : modelRing t j φ s) ∈
      Set.range (modelCoordinates t j φ s) := by
  obtain ⟨q, hq⟩ := exists_modelPolynomial t j φ s p hp
  refine ⟨Ideal.Quotient.mk _ q, ?_⟩
  apply CharacterFiniteCoefficientModel.inclusion_injective (values t j φ) (s ∪ {t})
  have h := RingHom.congr_fun (modelCoordinates_recovery t j φ s) (Ideal.Quotient.mk _ q)
  change modelInclusion t j φ s (modelCoordinates t j φ s (Ideal.Quotient.mk _ q)) =
    φ (modelChartMap t j φ s (Ideal.Quotient.mk _ q)) at h
  rw [h, modelChartMap_mk, hq, he]
  simp [CharacterFiniteCoefficientModel.inclusion]

end FLT.Mazur.OneGonFiniteCoefficientCoordinates

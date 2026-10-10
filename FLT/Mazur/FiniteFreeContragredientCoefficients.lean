/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFreeContragredient
public import FLT.Mazur.ProjectiveLinearCoefficientChange

/-!
# Coefficient compatibility of contragredient coordinates

The standard dual pairing commutes with every coefficient homomorphism.
Consequently any coefficient square of finite free isomorphisms induces the
same square on contragredient coordinates and their actual projective schemes.
-/

@[expose] public noncomputable section
open CategoryTheory
universe u
namespace FLT.Mazur.FiniteFreeContragredient
open ProjectiveSpace
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    {ι κ : Type u} [Finite ι] [Finite κ]

/-- The dual pairing is compatible with arbitrary changes of coefficient ring. -/
lemma dualCoordinates_coefficient (v w : ι →₀ R) :
    φ (dualCoordinates R ι v w) =
      dualCoordinates S ι (changeCoefficients φ v) (changeCoefficients φ w) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v z hv hz => simp [hv, hz]
  | single i r => simp [dualCoordinates_single_left, changeCoefficients]

/-- A coefficient square remains commutative after taking inverse transposes. -/
lemma map_coefficient (e : (ι →₀ R) ≃ₗ[R] (κ →₀ R))
    (d : (ι →₀ S) ≃ₗ[S] (κ →₀ S))
    (h : ∀ v, changeCoefficients φ (e v) = d (changeCoefficients φ v)) (v : ι →₀ R) :
    changeCoefficients φ (map e v) = map d (changeCoefficients φ v) := by
  ext j
  change φ (map e v j) = map d (changeCoefficients φ v) j
  rw [map_apply, map_apply, dualCoordinates_coefficient,
    changeCoefficients_inverse φ e d h, changeCoefficients_single, map_one]

/-- Dual homogeneous-generator changes commute with actual projective coefficient maps. -/
lemma projective_coefficient (e : (ι →₀ R) ≃ₗ[R] (κ →₀ R))
    (d : (ι →₀ S) ≃ₗ[S] (κ →₀ S))
    (h : ∀ v, changeCoefficients φ (e v) = d (changeCoefficients φ v)) :
    coefficientMap φ ι ≫ (linearIso (map e)).hom =
      (linearIso (map d)).hom ≫ coefficientMap φ κ :=
  linearIso_coefficientMap φ (map e) (map d) (map_coefficient φ e d h)

end FLT.Mazur.FiniteFreeContragredient

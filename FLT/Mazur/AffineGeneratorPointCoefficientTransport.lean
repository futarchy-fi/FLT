/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineGeneratorPointLinearTransport

/-!
# Dual transport after an arbitrary coefficient homomorphism

The original section vector and its transported vector may acquire their
invertible coordinates only after restriction. Polynomial evaluation gives
the actual projective transport law over that smaller coefficient ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MvPolynomial
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FiniteFreeContragredient
open ProjectiveSpace
variable {R S : Type u} [CommRing R] [CommRing S]
variable {ι κ : Type u} [Finite ι] [Finite κ]

omit [Finite ι] in
/-- Evaluation of a restricted vector is evaluation followed by the coefficient map. -/
lemma eval₂Hom_coefficients (φ : R →+* S) (v : ι → R) :
    eval₂Hom φ (fun i ↦ φ (v i)) = φ.comp (eval₂Hom (.id R) v) := by
  ext <;> simp

/-- The dual substitution transports restricted vectors over any coefficient ring. -/
lemma evaluate_contragredient_coefficients (φ : R →+* S)
    (e : (ι →₀ R) ≃ₗ[R] (κ →₀ R)) (v : ι →₀ R) :
    (eval₂Hom φ (fun i ↦ φ (v i))).comp
        (linearGradedMap (map e).symm.toLinearMap).toRingHom =
      eval₂Hom φ (fun j ↦ φ (e v j)) := by
  rw [eval₂Hom_coefficients, eval₂Hom_coefficients]
  apply RingHom.ext
  intro p
  exact congrArg φ (evaluate_contragredient_apply e v p)

/-- Original vector transport computes points even when units exist only after base change. -/
lemma unitChartPoint_transport_coefficients (φ : R →+* S)
    (e : (ι →₀ R) ≃ₗ[R] (κ →₀ R)) (v : ι →₀ R)
    (i : ι) (j : κ) (a b : Sˣ) (hi : φ (v i) = a) (hj : φ (e v j) = b) :
    unitChartPoint R ι φ (fun k ↦ φ (v k)) i a hi ≫ (linearIso (map e)).hom =
      unitChartPoint R κ φ (fun k ↦ φ (e v k)) j b hj :=
  unitChartPoint_linearIso_of_eval (map e) φ _ _
    (evaluate_contragredient_coefficients φ e v) i j a b hi hj

end FLT.Mazur.FiniteFreeContragredient

namespace FLT.Mazur.ProjectiveSpace
open FiniteFreeContragredient
variable {R : Type u} [CommRing R] {X : Scheme.{u}} [IsAffine X]
variable {ι κ : Type u} [Finite ι] [Finite κ]

/-- Affine generator transport over the actual structural coefficient map. -/
lemma affineGeneratorPoint_linearTransport_coefficients (φ : R →+* Γ(X, ⊤))
    (e : (ι →₀ R) ≃ₗ[R] (κ →₀ R)) (v : ι → R)
    (i : ι) (j : κ) (a b : Γ(X, ⊤)ˣ)
    (hi : φ (v i) = a) (hj : φ (functionCoordinates e v j) = b) :
    affineGeneratorPoint φ (fun k ↦ φ (v k)) i a hi ≫ (linearIso (map e)).hom =
      affineGeneratorPoint φ (fun k ↦ φ (functionCoordinates e v k)) j b hj := by
  rw [affineGeneratorPoint_eq_unitChartPoint, affineGeneratorPoint_eq_unitChartPoint,
    Category.assoc]
  apply congrArg (X.isoSpec.hom ≫ ·)
  exact unitChartPoint_transport_coefficients φ e
    ((Finsupp.linearEquivFunOnFinite R R ι).symm v) i j a b hi hj

end FLT.Mazur.ProjectiveSpace

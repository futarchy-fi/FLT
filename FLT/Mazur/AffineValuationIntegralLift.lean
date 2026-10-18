/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineValuationGeneratorLift
public import FLT.Mazur.OriginalPrimeIntegralEquations
public import FLT.Mazur.ValuationPoleEquations

/-!
# Constructing affine valuation lifts from original local integrality

Exact original equations force every generic coordinate into the valuation
ring. This constructs the entire scalar-compatible lift without requiring
finite type, reducedness, or an extension of any auxiliary boundary map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry IsLocalRing
namespace FLT.Mazur.AffineValuationGeneratorLift
open SchemeScalarPrincipalNeighborhood OriginalPrimeIntegralFiber
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {X : Scheme} [IsAffine X]
  (s : R →+* Γ(X, ⊤)) (S : ValuativeCommSq (scalarMorphism s))

omit [IsAffine X] in
/-- An exact equation with original leading coefficient outside the center excludes a pole. -/
theorem coordinates_mem_of_equation (b : Γ(X, ⊤)) (p : Polynomial R)
    (hp : p.eval₂ s b = 0)
    (hlead : p.leadingCoeff ∉ (S.i₂ (closedPoint S.R)).asIdeal) :
    genericCoordinates s S b ∈ (algebraMap S.R S.K).range := by
  by_contra hn
  have h := ValuationPoleReciprocal.original_leadingCoeff_mem S.R S.K
    s (centerCoordinates s S) (genericCoordinates s S) (coordinates_comm s S) b hn p hp
  change p.leadingCoeff ∈ (maximalIdeal S.R).comap (centerCoordinates s S) at h
  rw [center_comap_maximalIdeal] at h
  exact hlead h

omit [IsAffine X] in
/-- Local integrality at the center forces every original generic coordinate to be regular. -/
theorem coordinates_mem_of_localized_integral
    (h : (localizedMap s (S.i₂ (closedPoint S.R)).asIdeal).IsIntegral) (b : Γ(X, ⊤)) :
    genericCoordinates s S b ∈ (algebraMap S.R S.K).range := by
  obtain ⟨p, hp, hlead⟩ := exists_equation_of_localized_integral s
    (S.i₂ (closedPoint S.R)).asIdeal b (h _)
  exact coordinates_mem_of_equation s S b p hp hlead

/-- Local integrality constructs a full affine extension with both original triangle identities. -/
theorem hasLift_of_localized_integral
    (h : (localizedMap s (S.i₂ (closedPoint S.R)).asIdeal).IsIntegral) :
    S.commSq.HasLift := by
  obtain ⟨l, hl⟩ := FiniteGeneratorRingLift.exists_factor
    (algebraMap S.R S.K) (IsFractionRing.injective S.R S.K) (genericCoordinates s S)
    (coordinates_mem_of_localized_integral s S h)
  apply hasLift_of_coordinates s S l hl
  ext r
  apply IsFractionRing.injective S.R S.K
  exact (DFunLike.congr_fun hl (s r)).trans (DFunLike.congr_fun (coordinates_comm s S) r)

/-- Failure to extend produces an original coordinate with no equation invertible at the center. -/
theorem exists_coordinate_without_equation (h : ¬ S.commSq.HasLift) :
    ∃ b : Γ(X, ⊤), ∀ p : Polynomial R, p.eval₂ s b = 0 →
      p.leadingCoeff ∈ (S.i₂ (closedPoint S.R)).asIdeal := by
  by_contra hn
  push Not at hn
  apply h
  apply hasLift_of_localized_integral s S
  apply localizedMap_integral_of_numerators
  intro b
  exact (localized_integral_iff_equation s _ b).mpr (hn b)

end FLT.Mazur.AffineValuationGeneratorLift

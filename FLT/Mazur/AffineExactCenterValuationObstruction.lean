/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineValuationCoordinateSquare
public import FLT.Mazur.AffineValuationIntegralLift
public import FLT.Mazur.OriginalPrimeExactCenterValuations
public import FLT.Mazur.OriginalPrimeIntegralMinimalPrimes

/-!
# Geometric exact-center witnesses for failed component equations

A failed equation on a prime component gives an actual valuative square of
the original affine chart, centered at the original prime, with the same
coordinate pole. No extension, finite type, or completeness is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry IsLocalRing
namespace FLT.Mazur.AffineValuationGeneratorLift
open SchemeScalarPrincipalNeighborhood OriginalPrimeIntegralFiber
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {X : Scheme} [IsAffine X]
  (s : R →+* Γ(X, ⊤)) (P : PrimeSpectrum R)

/-- A domain-component equation failure produces a pole on the unchanged affine chart. -/
theorem exists_square_of_component_no_equation (Q : Ideal Γ(X, ⊤)) [Q.IsPrime]
    (b : Γ(X, ⊤))
    (he : ∀ p : Polynomial R,
      p.eval₂ ((Ideal.Quotient.mk Q).comp s) (Ideal.Quotient.mk Q b) = 0 →
        p.leadingCoeff ∈ P.asIdeal) :
    ∃ S : ValuativeCommSq (scalarMorphism s),
      S.i₂ (closedPoint S.R) = P ∧
        genericCoordinates s S b ∉ (algebraMap S.R S.K).range := by
  let sq := (Ideal.Quotient.mk Q).comp s
  let T := Localization (P.asIdeal.primeCompl.map sq)
  have hn : ¬ (localizedMap sq P.asIdeal).IsIntegral := fun hi ↦ by
    obtain ⟨p, hp, hl⟩ := exists_equation_of_localized_integral sq P.asIdeal
      (Ideal.Quotient.mk Q b) (hi _)
    exact hl (he p hp)
  let _ := localization_domain_of_not_integral sq P.asIdeal hn
  obtain ⟨V, f, hf, hc, hb⟩ :=
    exists_fraction_exact_center_pole sq P.asIdeal (Ideal.Quotient.mk Q b) he
  let g : Γ(X, ⊤) →+* FractionRing T :=
    (algebraMap T (FractionRing T)).comp
      ((algebraMap (Γ(X, ⊤) ⧸ Q) T).comp (Ideal.Quotient.mk Q))
  have hh : g.comp s = V.subtype.comp f := hf.symm
  let S := squareOfCoordinates s V f g hh
  refine ⟨S, ?_, ?_⟩
  · apply PrimeSpectrum.ext
    exact (squareOfCoordinates_center_ideal s V f g hh).trans hc
  · change genericCoordinates s (squareOfCoordinates s V f g hh) b ∉ _
    rw [squareOfCoordinates_generic]
    rintro ⟨v, hv⟩
    apply hb
    change g b ∈ V
    have hv' : (v : V).val = g b := hv
    exact hv' ▸ (v : V).property

/-- Failure of local integrality selects a fixed generator and an exact-center scheme pole. -/
theorem exists_generator_square_of_not_integral
    (hfin : (minimalPrimes Γ(X, ⊤)).Finite) (G : Set Γ(X, ⊤))
    (hgen : Subring.closure (Set.range s ∪ G) = ⊤)
    (h : ¬ (localizedMap s P.asIdeal).IsIntegral) :
    ∃ S : ValuativeCommSq (scalarMorphism s), S.i₂ (closedPoint S.R) = P ∧
      ∃ b ∈ G, genericCoordinates s S b ∉ (algebraMap S.R S.K).range := by
  obtain ⟨b, hb, Q, hQ, he⟩ :=
    exists_minimal_generator_obstruction s P.asIdeal hfin G hgen h
  let _ := hQ.isPrime
  obtain ⟨S, hc, hp⟩ := exists_square_of_component_no_equation s P Q b he
  exact ⟨S, hc, b, hb, hp⟩

/-- Exact-center regularity of the fixed generators reconstructs original local integrality. -/
theorem localizedMap_integral_of_centered_generator_regular
    (hfin : (minimalPrimes Γ(X, ⊤)).Finite) (G : Set Γ(X, ⊤))
    (hgen : Subring.closure (Set.range s ∪ G) = ⊤)
    (h : ∀ S : ValuativeCommSq (scalarMorphism s), S.i₂ (closedPoint S.R) = P →
      ∀ b ∈ G, genericCoordinates s S b ∈ (algebraMap S.R S.K).range) :
    (localizedMap s P.asIdeal).IsIntegral := by
  by_contra hn
  obtain ⟨S, hc, b, hb, hp⟩ :=
    exists_generator_square_of_not_integral s P hfin G hgen hn
  exact hp (h S hc b hb)

/-- With finitely many domain components, local integrality is exactly the centered lift test. -/
theorem localizedMap_integral_iff_centered_lifts
    (hfin : (minimalPrimes Γ(X, ⊤)).Finite) :
    (localizedMap s P.asIdeal).IsIntegral ↔
      ∀ S : ValuativeCommSq (scalarMorphism s),
        S.i₂ (closedPoint S.R) = P → S.commSq.HasLift := by
  refine ⟨fun hi S hc ↦ ?_, fun h ↦ ?_⟩
  · apply hasLift_of_localized_integral s S
    rwa [hc]
  · apply localizedMap_integral_of_centered_generator_regular s P hfin Set.univ
      (by simp only [Set.union_univ, Subring.closure_univ])
    intro S hc b _
    obtain ⟨l⟩ := (CommSq.HasLift.iff _).mp (h S hc)
    rw [coordinates_of_lift s S l]
    exact ⟨_, rfl⟩

end FLT.Mazur.AffineValuationGeneratorLift

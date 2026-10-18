/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeBadAffineCoverIntegralLocus
public import FLT.Mazur.OriginalPrimeIntegralMinimalPrimes

/-!
# Finite domain tests for the actual bad affine atlas

Integer finite type proves that every bad-chart coordinate ring is Noetherian.
Its finitely many minimal domain quotients therefore detect original local
integrality. A failed test identifies an original generator on an actual component.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.SchemeBadAffineCover
open OriginalPrimeIntegralFiber
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {X : Scheme} [NoetherianSpace X]
  (s : R →+* Γ(X, ⊤)) (O : X.Opens)
  (g : X ⟶ Spec (.of ℤ)) [LocallyOfFiniteType g]

include g in
/-- Integer finite type makes each bad-chart coordinate ring Noetherian. -/
theorem badChart_noetherianRing (i : (badCover O).I₀) :
    IsNoetherianRing Γ((badCover O).X i, ⊤) := by
  have : LocallyOfFiniteType (badChartMap O i ≫ g) := by
    change LocallyOfFiniteType ((badCover O).f i ≫ badInclusion O ≫ g)
    infer_instance
  let _ := LocallyOfFiniteType.isLocallyNoetherian (badChartMap O i ≫ g)
  exact IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩

include g in
/-- The domain components form a finite family before any scalar prime is selected. -/
theorem badChart_minimalPrimes_finite (i : (badCover O).I₀) :
    (minimalPrimes Γ((badCover O).X i, ⊤)).Finite := by
  let _ := badChart_noetherianRing O g i
  exact minimalPrimes.finite_of_isNoetherianRing _

/-- The original scalar map on one minimal component of one actual bad chart. -/
def badComponentScalar (i : (badCover O).I₀)
    (Q : minimalPrimes Γ((badCover O).X i, ⊤)) :
    R →+* (Γ((badCover O).X i, ⊤) ⧸ Q.val) :=
  (Ideal.Quotient.mk Q.val).comp (badChartScalar s O i)

/-- Every component target is a domain; no reduction of the scalar ring is made. -/
theorem badComponent_isDomain (i : (badCover O).I₀)
    (Q : minimalPrimes Γ((badCover O).X i, ⊤)) :
    IsDomain (Γ((badCover O).X i, ⊤) ⧸ Q.val) := by
  let _ := Q.property.isPrime
  infer_instance

include g in
/-- The same original prime tests the full chart exactly when it tests each domain component. -/
theorem badChart_integral_iff_components (P : PrimeSpectrum R) (i : (badCover O).I₀) :
    (localizedMap (badChartScalar s O i) P.asIdeal).IsIntegral ↔
      ∀ Q : minimalPrimes Γ((badCover O).X i, ⊤),
        (localizedMap (badComponentScalar s O i Q) P.asIdeal).IsIntegral := by
  rw [localizedMap_integral_iff_minimal_components _ _ (badChart_minimalPrimes_finite O g i)]
  exact ⟨fun h Q ↦ h Q.val Q.property, fun h Q hQ ↦ h ⟨Q, hQ⟩⟩

attribute [local irreducible] badChartGenerators

/-- Component equations of the fixed finite chart generators suffice for the entire atlas. -/
theorem badCharts_integral_of_component_generator_equations (P : PrimeSpectrum R)
    (he : ∀ (i : (badCover O).I₀) (b : Γ((badCover O).X i, ⊤)),
      b ∈ badChartGenerators s O g i → ∀ Q : minimalPrimes Γ((badCover O).X i, ⊤),
        ∃ p : Polynomial R,
          p.eval₂ (badComponentScalar s O i Q) (Ideal.Quotient.mk Q.val b) = 0 ∧
            p.leadingCoeff ∉ P.asIdeal) :
    ∀ i, (localizedMap (badChartScalar s O i) P.asIdeal).IsIntegral := by
  intro i
  apply localizedMap_integral_of_minimal_generator_equations _ _
    (badChart_minimalPrimes_finite O g i)
    (badChartGenerators s O g i : Set Γ((badCover O).X i, ⊤))
    (badChartGenerators_generate s O g i)
  exact fun b hb Q hQ ↦ he i b hb ⟨Q, hQ⟩

/-- A failed chart supplies a fixed generator on a domain component with no avoiding equation. -/
theorem badChart_generator_component_obstruction (P : PrimeSpectrum R) (i : (badCover O).I₀)
    (h : ¬ (localizedMap (badChartScalar s O i) P.asIdeal).IsIntegral) :
    ∃ b ∈ badChartGenerators s O g i,
      ∃ Q : minimalPrimes Γ((badCover O).X i, ⊤), ∀ p : Polynomial R,
        p.eval₂ (badComponentScalar s O i Q) (Ideal.Quotient.mk Q.val b) = 0 →
          p.leadingCoeff ∈ P.asIdeal := by
  obtain ⟨b, hb, Q, hQ, he⟩ := exists_minimal_generator_obstruction _ _
    (badChart_minimalPrimes_finite O g i)
    (badChartGenerators s O g i : Set Γ((badCover O).X i, ⊤))
    (badChartGenerators_generate s O g i) h
  exact ⟨b, hb, ⟨Q, hQ⟩, he⟩

end FLT.Mazur.SchemeBadAffineCover

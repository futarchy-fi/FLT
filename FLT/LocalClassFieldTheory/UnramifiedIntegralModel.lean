/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedStages
public import FLT.LocalClassFieldTheory.FrobeniusTower

/-!
# Canonical integral models of unramified stages

The existential DVR in a constructed stage is its integral closure. Uniqueness
of integral closures transports the DVR and unramified structures to the
canonical subring; neither property is an extra bridge hypothesis.
-/

@[expose] public noncomputable section

universe u

namespace LocalClassFieldTheory

open IsLocalRing

variable {R K E : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field E] [Algebra K E] [Algebra R E] [IsScalarTower R K E]

omit [IsDomain R] [IsDiscreteValuationRing R] [Algebra R K] [IsFractionRing R K]
  [IsScalarTower R K E] in
/-- Every constructed stage has a canonical integral closure which is a DVR. -/
theorem IsUnramifiedStage.canonical_dvr (h : IsUnramifiedStage R K E) :
    IsDiscreteValuationRing (integralClosure R E) := by
  obtain ⟨_, S, _, _, _, _, _, _, _, _, _, _, _⟩ := h
  let : IsIntegralClosure S R E := IsIntegralClosure.of_isIntegrallyClosed S R E
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (IsIntegralClosure.equiv R S E (integralClosure R E))

omit [IsDomain R] [IsDiscreteValuationRing R] [Algebra R K] [IsFractionRing R K]
  [IsScalarTower R K E] in
/-- Formal unramifiedness holds for the canonical integral closure itself. -/
theorem IsUnramifiedStage.canonical_unramified (h : IsUnramifiedStage R K E) :
    Algebra.FormallyUnramified R (integralClosure R E) := by
  obtain ⟨_, S, _, _, _, _, _, _, _, _, _, hu, _⟩ := h
  let := hu
  let : IsIntegralClosure S R E := IsIntegralClosure.of_isIntegrallyClosed S R E
  exact Algebra.FormallyUnramified.of_equiv
    (IsIntegralClosure.equiv R S E (integralClosure R E))

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- A change of fraction-field presentation preserves the actual integral model. -/
theorem IsUnramifiedStage.of_algEquiv (h : IsUnramifiedStage R K E)
    {F : Type u} [Field F] [Algebra K F] [Algebra R F] [IsScalarTower R K F]
    (e : E ≃ₐ[K] F) : IsUnramifiedStage R K F := by
  obtain ⟨_, S, _, _, _, _, _, _, _, _, _, hu, hh⟩ := h
  let : FiniteDimensional K F := e.toLinearEquiv.finiteDimensional
  let algSF : Algebra S F := (e.toRingHom.comp (algebraMap S E)).toAlgebra
  let es : E ≃ₐ[S] F := { e.toRingEquiv with commutes' := fun _ => rfl }
  let : IsFractionRing S F := IsFractionRing.of_algEquiv es
  let : IsScalarTower R S F := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R F r = e (algebraMap S E (algebraMap R S r))
    rw [← IsScalarTower.algebraMap_apply R S E,
      IsScalarTower.algebraMap_apply R K E, e.commutes,
      ← IsScalarTower.algebraMap_apply R K F]
  exact ⟨inferInstance, S, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, algSF, inferInstance, inferInstance, hu, hh⟩

end LocalClassFieldTheory

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedLocalInertia
public import FLT.AbsoluteGaloisGroup.InertiaDescentUniformizer

/-!
# Finite fields fixed by inertia are constructed unramified stages

Trivial inertia gives ramification index one by the existing finite local
comparison. A base uniformizer remains irreducible, so the canonical integral
closure is a DVR, is formally unramified, and is Henselian over a complete base.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing IsDiscreteValuationRing NumberField

variable {F : Type} [Field F] [NumberField F]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))

local notation "K" => v.adicCompletion F
local notation "R" => v.adicCompletionIntegers F

variable [IsAdicComplete (maximalIdeal (v.adicCompletionIntegers F))
  (v.adicCompletionIntegers F)]
  (E : IntermediateField (v.adicCompletion F) (AlgebraicClosure (v.adicCompletion F)))
  [FiniteDimensional (v.adicCompletion F) E] [IsGalois (v.adicCompletion F) E]

/-- A finite Galois field fixed by valuation inertia has an actual unramified DVR model. -/
theorem isUnramifiedStage_of_local_inertia_le
    (h : localInertiaGroup v ≤ E.fixingSubgroup) : IsUnramifiedStage R K E := by
  have hi : (maximalIdeal (IntegralClosure R E)).inertia Gal(E/K) = ⊥ := by
    rw [← map_localInertiaGroup_eq_inertia, Subgroup.map_eq_bot_iff,
      IntermediateField.restrictNormalHom_ker]
    exact h
  have he := ramificationIdx_eq_one_of_inertia_eq_bot v E hi
  let S := IntegralClosure R E
  let : IsFractionRing S E := integralClosure.isFractionRing_of_finite_extension K E
  let : IsIntegralClosure S R E := by
    change IsIntegralClosure (integralClosure R E) R E
    infer_instance
  let : Module.Finite R S := IsIntegralClosure.finite R K E S
  let : IsDedekindDomain S := IsIntegralClosure.isDedekindDomain R K E S
  obtain ⟨π, hπ⟩ := exists_irreducible R
  have hπS : Irreducible (algebraMap R S π) :=
    irreducible_map_of_ramificationIdx_eq_one hπ he
  let : IsDiscreteValuationRing S := {
    not_a_field' := by
      intro hm
      have hx := hπS.not_isUnit
      change algebraMap R S π ∈ maximalIdeal S at hx
      rw [hm, Ideal.mem_bot] at hx
      exact hπS.ne_zero hx }
  have hm : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S := by
    rw [hπ.maximalIdeal_eq, hπS.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  let : Algebra.FormallyUnramified R S :=
    Algebra.FormallyUnramified.of_map_maximalIdeal hm
  let : HenselianLocalRing S := RaynaudParameters.unramified_stage_henselian hm
  exact ⟨inferInstance, S, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance⟩

/-- The constructed stage condition agrees with trivial local inertia on finite Galois fields. -/
theorem isUnramifiedStage_iff_local_inertia_le :
    IsUnramifiedStage R K E ↔ localInertiaGroup v ≤ E.fixingSubgroup :=
  ⟨fun h => h.local_inertia_le_fixingSubgroup v E,
    isUnramifiedStage_of_local_inertia_le v E⟩

end LocalClassFieldTheory

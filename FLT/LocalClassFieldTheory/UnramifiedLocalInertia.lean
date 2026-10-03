/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedIntegralModel
public import FLT.AbsoluteGaloisGroup.Unramified

/-!
# Constructed unramified stages and local valuation inertia

At a number-field completion, the canonical integral closure is exactly the
ring used by the existing local inertia comparison. Faithful reduction of the
constructed integral model therefore makes local inertia fix the stage.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing NumberField

variable {F : Type} [Field F] [NumberField F]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))

local notation "K" => v.adicCompletion F
local notation "R" => v.adicCompletionIntegers F

variable (E : IntermediateField (v.adicCompletion F) (AlgebraicClosure (v.adicCompletion F)))
  [FiniteDimensional (v.adicCompletion F) E] [IsGalois (v.adicCompletion F) E]

/-- The canonical ideal inertia of a constructed unramified stage is trivial. -/
theorem IsUnramifiedStage.local_inertia_eq_bot (h : IsUnramifiedStage R K E) :
    (maximalIdeal (IntegralClosure R E)).inertia Gal(E/K) = ⊥ := by
  let S := IntegralClosure R E
  let : IsDiscreteValuationRing S := h.canonical_dvr
  let : Algebra.FormallyUnramified R S := h.canonical_unramified
  let : IsFractionRing S E := integralClosure.isFractionRing_of_finite_extension K E
  let : IsIntegralClosure S R E := by
    change IsIntegralClosure (integralClosure R E) R E
    infer_instance
  let : Module.Finite R S := IsIntegralClosure.finite R K E S
  apply bot_unique
  intro σ hσ
  change σ = 1
  apply residueGaloisAction_injective R S K E
  rw [map_one]
  apply (residueAction_eq_one_iff R S _).mpr
  intro x
  have hx : galRestrict R K E S σ x = σ • x := by
    apply Subtype.ext
    exact algebraMap_galRestrict_apply R σ x
  change galRestrict R K E S σ x - x ∈ maximalIdeal S
  rw [hx]
  exact hσ x

/-- Existing local valuation inertia fixes every element of a constructed stage. -/
theorem IsUnramifiedStage.local_inertia_le_fixingSubgroup (h : IsUnramifiedStage R K E) :
    localInertiaGroup v ≤ E.fixingSubgroup := by
  rw [← IntermediateField.restrictNormalHom_ker, ← Subgroup.map_eq_bot_iff,
    map_localInertiaGroup_eq_inertia]
  exact h.local_inertia_eq_bot v E

end LocalClassFieldTheory

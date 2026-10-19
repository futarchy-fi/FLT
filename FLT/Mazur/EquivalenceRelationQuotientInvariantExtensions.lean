/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompatibleQuotientCorrections

/-!
# Extending complete-stage invariants to the original ambient chart

Freeness lifts any specified finite-stage invariant to an ambient invariant.
Restricting that lift gives a compatible invariant family at all orders,
retaining the prescribed coefficient. No extension of an arbitrary infinite
family to the original chart is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source action restrictedAction
variable {D A : Scheme} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (U : (source p q I o).Opens)
  (hU : ∀ g : Equiv.Perm I, (action e I o g).hom ⁻¹ᵁ U = U)
  [IsAffine U.toScheme]
local notation "ρ" => restrictedAction (action e I o) U hU
local notation "α" k => completeQuotientFrameAction e I o U hU k
local notation "π" k => pullback.fst (quotientMap ρ) (completeQuotientStageMap e I o U hU k)

/-- The full original chart projection from each quotient stage is equivariant. -/
@[reassoc] theorem completeQuotientFrame_fst_equivariant (k : ℕ) (g : Equiv.Perm I) :
    ((α k) g).hom ≫ (π k) = (π k) ≫ (ρ g).hom :=
  FiniteGroupPullback.action_fst ρ (quotientMap ρ) (quotientMap_invariant ρ)
    (completeQuotientStageMap e I o U hU k) g

/-- Restrict ambient invariants using the original, unreduced coefficient maps. -/
def completeQuotientInvariantRestriction (k : ℕ) :
    invariantCoordinates ρ →+* invariantCoordinates (α k) :=
  invariantMap (α k) ρ (π k) (completeQuotientFrame_fst_equivariant e I o U hU k)

/-- Every finite-stage invariant extends to the original ambient affine chart. -/
theorem completeQuotientInvariantRestriction_surjective (k : ℕ) :
    Function.Surjective (completeQuotientInvariantRestriction e I o U hU k) := by
  apply invariantMap_surjective_of_free ρ
    (fun _ _ a g ha ↦ completeSource_action_free e I o U.ι ρ
      (restrictedAction_hom_ι (action e I o) U hU) a g ha)

/-- Pull back invariant coefficients along the actual quotient tower transitions. -/
def completeQuotientInvariantTransition {m n : ℕ} (h : m ≤ n) :
    invariantCoordinates (α n) →+* invariantCoordinates (α m) :=
  invariantMap (α m) (α n) (completeQuotientFrameTransition e I o U hU h)
    (completeQuotientFrameTransition_equivariant e I o U hU h)

/-- Ambient restriction is compatible as an equality in the full invariant rings. -/
theorem completeQuotientInvariantRestriction_transition (v : invariantCoordinates ρ)
    {m n : ℕ} (h : m ≤ n) :
    completeQuotientInvariantTransition e I o U hU h
      (completeQuotientInvariantRestriction e I o U hU n v) =
        completeQuotientInvariantRestriction e I o U hU m v := by
  apply Subtype.ext
  exact completeQuotientCoefficient_transition e I o U hU v.val h

/-- Each invariant transition is surjective, with no averaging denominator. -/
theorem completeQuotientInvariantTransition_surjective {m n : ℕ} (h : m ≤ n) :
    Function.Surjective (completeQuotientInvariantTransition e I o U hU h) := by
  intro t
  obtain ⟨v, hv⟩ := completeQuotientInvariantRestriction_surjective e I o U hU m t
  exact ⟨completeQuotientInvariantRestriction e I o U hU n v,
    (completeQuotientInvariantRestriction_transition e I o U hU v h).trans hv⟩

/-- A prescribed invariant at any order extends compatibly to every order. -/
theorem exists_completeQuotient_invariant_family (k : ℕ) (t : invariantCoordinates (α k)) :
    ∃ v : ∀ n, invariantCoordinates (α n), v k = t ∧
      ∀ m n (h : m ≤ n), completeQuotientInvariantTransition e I o U hU h (v n) = v m := by
  obtain ⟨a, ha⟩ := completeQuotientInvariantRestriction_surjective e I o U hU k t
  exact ⟨fun n ↦ completeQuotientInvariantRestriction e I o U hU n a, ha,
    fun _ _ h ↦ completeQuotientInvariantRestriction_transition e I o U hU a h⟩

end FLT.Mazur.EquivalenceRelationNormalizedFrames

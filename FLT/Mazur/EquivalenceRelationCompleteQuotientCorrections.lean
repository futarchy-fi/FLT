/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteQuotientStages

/-!
# Exact boundary corrections over the constructed complete quotient stages

The actual positive-power quotient stages supply completeness independently
of a boundary lift. Freeness constructs a lift of every invariant boundary
value; its subtraction is an exact boundary-zero correction for the full
original relation. The finite flat cover also detects all coefficient powers.
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
  [IsAffine U.toScheme] (k : ℕ)
local notation "S" => completeQuotientFrame e I o U hU k
local notation "j" => completeQuotientFrameInclusion e I o U hU k
local notation "τ" => completeQuotientFrameAction e I o U hU k
local notation "hj" => completeQuotientFrameAction_inclusion e I o U hU k
local notation "π" => completeQuotientFrameCover e I o U hU k

/-- The constructed complete quotient cover loses no stage coefficients. -/
theorem completeQuotientFrame_coefficients_injective : Function.Injective (π).appTop :=
  SchemeEffectiveEpiSections.appTop_injective π

/-- Nilpotence is detected on the actual frame cover at the same exponent. -/
theorem completeQuotientFrame_power_iff
    (J : Ideal Γ(completeQuotientStage e I o U hU k, ⊤)) (m : ℕ) :
    (J.map (π).appTop.hom) ^ m = ⊥ ↔ J ^ m = ⊥ := by
  rw [← Ideal.map_pow]
  exact Ideal.map_eq_bot_iff_of_injective
    (completeQuotientFrame_coefficients_injective e I o U hU k)

/-- Full kernel-pair compatibility descends a unique coefficient to the power quotient. -/
theorem completeQuotientFrame_sections (t : Γ(S, ⊤))
    (ht : (pullback.fst π π).appTop t = (pullback.snd π π).appTop t) :
    ∃! a : Γ(completeQuotientStage e I o U hU k, ⊤), (π).appTop a = t :=
  SchemeEffectiveEpiSections.sections_existsUnique (IsPullback.of_hasPullback π π) t ht

/-- Every moving invariant satisfies the entire original relation on this constructed stage. -/
theorem completeQuotientFrame_invariant_equalizes (t : invariantCoordinates τ) :
    (SourceRestriction.fst j j).appTop t.val = (SourceRestriction.snd j j).appTop t.val :=
  completeEquivariant_invariant_equalizes e I o j τ hj
    (completeQuotientFrame_complete e I o U hU k) t

variable {B : Scheme} (i : B ⟶ source p q I o) [IsClosedImmersion i]
  (ρ : Equiv.Perm I →* Aut B)
  (hi : ∀ g, (ρ g).hom ≫ i = i ≫ (action e I o g).hom)
local notation "β" => FiniteGroupEquivariantPullback.action τ ρ (action e I o) j i hj hi
local notation "b" => pullback.fst j i
local notation "hb" => FiniteGroupEquivariantPullback.action_fst τ ρ (action e I o) j i hj hi

/-- Every original invariant boundary value has an invariant complete-stage lift. -/
theorem completeQuotientFrame_boundary_surjective :
    Function.Surjective (invariantMap β τ b hb) :=
  completeBoundary_invariant_surjective e I o j τ hj i ρ hi

/-- The actual stage constructs boundary-zero corrections with the full original discrepancy. -/
theorem completeQuotientFrame_boundary_correction
    (t : invariantCoordinates β) (u : Γ(S, ⊤)) (hu : (b).appTop u = t.val) :
    ∃ z : Γ(S, ⊤), (b).appTop z = 0 ∧
      (SourceRestriction.fst j j).appTop z - (SourceRestriction.snd j j).appTop z =
        (SourceRestriction.fst j j).appTop u - (SourceRestriction.snd j j).appTop u :=
  completeBoundary_exists_kernel_correction e I o j τ hj i ρ hi
    (completeQuotientFrame_complete e I o U hU k) t u hu

omit [IsClosedImmersion i] in
/-- All boundary nilpotents are preserved by extension of the invariant boundary kernel. -/
theorem completeQuotientFrame_boundary_kernel :
    (RingHom.ker (invariantMap β τ b hb)).map
      (let _ := SchemeCoordinateAction.coordinateAction τ
       FiniteGroupQuotient.inclusion (Equiv.Perm I) Γ(S, ⊤)) =
        RingHom.ker (b).appTop.hom :=
  completeBoundary_kernel_extension e I o j τ hj i ρ hi

end FLT.Mazur.EquivalenceRelationNormalizedFrames

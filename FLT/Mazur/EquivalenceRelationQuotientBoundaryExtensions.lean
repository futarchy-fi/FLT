/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineClosedBoundaryKernelLifting
public import FLT.Mazur.EquivalenceRelationQuotientInvariantExtensions

/-!
# Extending finite-stage boundary corrections to the original chart

Every exact boundary-zero coefficient at a complete quotient stage lifts to
the ambient boundary kernel. Together with invariant extension this lifts a
prescribed stage input and its correction to one ambient pair, which gives
compatible exact corrections at all orders. The ambient input is constructed,
not identified with a separately prescribed ambient input.
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
local notation "j" k => completeQuotientFrameInclusion e I o U hU k
local notation "π" k => pullback.fst (quotientMap ρ) (completeQuotientStageMap e I o U hU k)
local notation "coeff" a:max k:max => completeQuotientCoefficient e I o U hU a k
variable {B : Scheme} (i : B ⟶ source p q I o) [IsClosedImmersion i]

/-- All boundary-zero stage coefficients extend to the exact original ambient boundary kernel. -/
theorem completeQuotient_boundary_zero_lift (k : ℕ)
    (z : Γ(completeQuotientFrame e I o U hU k, ⊤))
    (hz : (pullback.fst (j k) i).appTop z = 0) :
    ∃ a : Γ(U.toScheme, ⊤), (pullback.fst U.ι i).appTop a = 0 ∧ coeff a k = z := by
  let _ : IsAffine (pullback U.ι i) := isAffine_of_isAffineHom (pullback.fst U.ι i)
  apply AffineClosedBoundaryKernelLifting.exists_boundary_zero_lift
    (π k) (pullback.fst U.ι i) z
  have he := pullbackRightPullbackFstIso_hom_fst U.ι i (π k)
  rw [← he, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  change (pullbackRightPullbackFstIso U.ι i (π k)).hom.appTop
    ((pullback.fst (j k) i).appTop z) = 0
  rw [hz, map_zero]

/-- A stage correction and its invariant difference extend together to a single ambient pair. -/
theorem completeQuotient_correction_pair_lift (k : ℕ)
    (a z : Γ(completeQuotientFrame e I o U hU k, ⊤))
    (hz : (pullback.fst (j k) i).appTop z = 0)
    (v : invariantCoordinates (α k)) (hv : a - z = v.val) :
    ∃ a' z' : Γ(U.toScheme, ⊤), (pullback.fst U.ι i).appTop z' = 0 ∧
      coeff a' k = a ∧ coeff z' k = z ∧
      ∃ v' : invariantCoordinates ρ, a' - z' = v'.val := by
  obtain ⟨z', hz', he⟩ := completeQuotient_boundary_zero_lift e I o U hU i k z hz
  obtain ⟨v', hv'⟩ := completeQuotientInvariantRestriction_surjective e I o U hU k v
  have he' : (π k).appTop v'.val = v.val := congrArg Subtype.val hv'
  refine ⟨z' + v'.val, z', hz', ?_, he, v', ?_⟩
  · change (π k).appTop (z' + v'.val) = a
    rw [map_add, show (π k).appTop z' = z from he, he', ← hv]
    ring
  · ring

variable (τ : Equiv.Perm I →* Aut B)
  (hi : ∀ g, (τ g).hom ≫ i = i ≫ (action e I o g).hom)
local notation "hj" k => completeQuotientFrameAction_inclusion e I o U hU k
local notation "β" k => FiniteGroupEquivariantPullback.action
  (α k) τ (action e I o) (j k) i (hj k) hi

/-- Any finite-stage invariant boundary datum has a compatible ambient correction pair. -/
theorem exists_completeQuotient_boundary_pair_lift (k : ℕ)
    (t : invariantCoordinates (β k)) (a : Γ(completeQuotientFrame e I o U hU k, ⊤))
    (ha : (pullback.fst (j k) i).appTop a = t.val) :
    ∃ a' z' : Γ(U.toScheme, ⊤), (pullback.fst U.ι i).appTop z' = 0 ∧
      coeff a' k = a ∧
      ∀ r : ℕ,
        (pullback.fst (j r) i).appTop (coeff z' r) = 0 ∧
        (SourceRestriction.fst (j r) (j r)).appTop (coeff z' r) -
          (SourceRestriction.snd (j r) (j r)).appTop (coeff z' r) =
        (SourceRestriction.fst (j r) (j r)).appTop (coeff a' r) -
          (SourceRestriction.snd (j r) (j r)).appTop (coeff a' r) := by
  obtain ⟨z, hz, v, hv⟩ :=
    exists_ambient_boundary_correction e I o (j k) (α k) (hj k) i τ hi t a ha
  obtain ⟨a', z', hz', ha', _, v', hv'⟩ :=
    completeQuotient_correction_pair_lift e I o U hU i k a z hz v hv
  exact ⟨a', z', hz', ha', fun r ↦
    ⟨completeQuotientCoefficient_boundary_zero e I o U hU i z' hz' r,
      completeQuotientCoefficient_correction e I o U hU a' z' v' hv' r⟩⟩

end FLT.Mazur.EquivalenceRelationNormalizedFrames

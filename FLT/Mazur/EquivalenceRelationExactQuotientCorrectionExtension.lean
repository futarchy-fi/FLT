/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationPrescribedQuotientCorrection
public import FLT.Mazur.EquivalenceRelationEqualizedInvariants

/-!
# Extending exact finite-stage solutions for a fixed original input

An exact correction equation supplies its own invariant difference. Thus every
boundary-zero finite-stage solution for the prescribed ambient input extends
back to that same input and to compatible exact solutions at every order.
No arbitrary infinite family is asserted to extend to the ambient ring.
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
local notation "hj" => restrictedAction_hom_ι (action e I o) U hU
local notation "α" k => completeQuotientFrameAction e I o U hU k
local notation "j" k => completeQuotientFrameInclusion e I o U hU k
local notation "π" k => pullback.fst (quotientMap ρ) (completeQuotientStageMap e I o U hU k)
local notation "coeff" a:max k:max => completeQuotientCoefficient e I o U hU a k
variable {B : Scheme} (i : B ⟶ source p q I o) [IsClosedImmersion i]
  (τ : Equiv.Perm I →* Aut B)
  (hi : ∀ g, (τ g).hom ≫ i = i ≫ (action e I o g).hom)
local notation "β" => FiniteGroupEquivariantPullback.action ρ τ (action e I o) U.ι i hj hi
local notation "b" => pullback.fst U.ι i
local notation "hb" => FiniteGroupEquivariantPullback.action_fst ρ τ (action e I o) U.ι i hj hi

/-- An exact stage equation suffices to interpolate a prescribed correction in the ambient chart. -/
theorem completeQuotient_exact_correction_lift
    (t : invariantCoordinates β) (a : Γ(U.toScheme, ⊤)) (ha : (b).appTop a = t.val)
    (k : ℕ) (z : Γ(completeQuotientFrame e I o U hU k, ⊤))
    (hz : (pullback.fst (j k) i).appTop z = 0)
    (he : (SourceRestriction.fst (j k) (j k)).appTop z -
        (SourceRestriction.snd (j k) (j k)).appTop z =
      (SourceRestriction.fst (j k) (j k)).appTop (coeff a k) -
        (SourceRestriction.snd (j k) (j k)).appTop (coeff a k)) :
    ∃ z' : Γ(U.toScheme, ⊤), (b).appTop z' = 0 ∧ coeff z' k = z ∧
      ∃ v' : invariantCoordinates ρ, a - z' = v'.val := by
  obtain ⟨v, hv⟩ := exists_invariant_of_original_correction e I o (j k) (α k)
    (completeQuotientFrameAction_inclusion e I o U hU k) (coeff a k) z he
  exact completeQuotient_prescribed_correction_lift e I o U hU i τ hi t a ha k z hz v hv

/-- Every exact finite solution extends to one ambient correction and all later exact solutions. -/
theorem completeQuotient_exact_correction_all_orders
    (t : invariantCoordinates β) (a : Γ(U.toScheme, ⊤)) (ha : (b).appTop a = t.val)
    (k : ℕ) (z : Γ(completeQuotientFrame e I o U hU k, ⊤))
    (hz : (pullback.fst (j k) i).appTop z = 0)
    (he : (SourceRestriction.fst (j k) (j k)).appTop z -
        (SourceRestriction.snd (j k) (j k)).appTop z =
      (SourceRestriction.fst (j k) (j k)).appTop (coeff a k) -
        (SourceRestriction.snd (j k) (j k)).appTop (coeff a k)) :
    ∃ z' : Γ(U.toScheme, ⊤), (b).appTop z' = 0 ∧ coeff z' k = z ∧
      ∀ r : ℕ,
        (pullback.fst (j r) i).appTop (coeff z' r) = 0 ∧
        (SourceRestriction.fst (j r) (j r)).appTop (coeff z' r) -
          (SourceRestriction.snd (j r) (j r)).appTop (coeff z' r) =
        (SourceRestriction.fst (j r) (j r)).appTop (coeff a r) -
          (SourceRestriction.snd (j r) (j r)).appTop (coeff a r) := by
  obtain ⟨v, hv⟩ := exists_invariant_of_original_correction e I o (j k) (α k)
    (completeQuotientFrameAction_inclusion e I o U hU k) (coeff a k) z he
  exact completeQuotient_prescribed_correction_all_orders
    e I o U hU i τ hi t a ha k z hz v hv

end FLT.Mazur.EquivalenceRelationNormalizedFrames

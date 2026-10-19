/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationQuotientBoundaryExtensions
public import FLT.Mazur.SchemeFiniteGroupPrescribedBoundaryCorrection

/-!
# Prescribed ambient inputs and prescribed finite quotient corrections

Extend a supplied correction on one complete quotient stage while retaining
the supplied ambient input and its original boundary value. The single ambient
correction then satisfies the exact original equations at every quotient order.
This does not assert completeness of any additional original scalar fiber.
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

/-- Interpolate the exact stage correction without replacing the given ambient input. -/
theorem completeQuotient_prescribed_correction_lift
    (t : invariantCoordinates β) (a : Γ(U.toScheme, ⊤)) (ha : (b).appTop a = t.val)
    (k : ℕ) (z : Γ(completeQuotientFrame e I o U hU k, ⊤))
    (hz : (pullback.fst (j k) i).appTop z = 0)
    (v : invariantCoordinates (α k)) (hv : coeff a k - z = v.val) :
    ∃ z' : Γ(U.toScheme, ⊤), (b).appTop z' = 0 ∧ coeff z' k = z ∧
      ∃ v' : invariantCoordinates ρ, a - z' = v'.val := by
  apply exists_prescribed_boundary_correction ρ
    (fun _ _ u g hu ↦ completeSource_action_free e I o U.ι ρ hj u g hu)
    (α k) (π k) (completeQuotientFrame_fst_equivariant e I o U hU k)
    β b hb t a ha z _ v hv
  have he := pullbackRightPullbackFstIso_hom_fst U.ι i (π k)
  rw [← he, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  change (pullbackRightPullbackFstIso U.ι i (π k)).hom.appTop
    ((pullback.fst (j k) i).appTop z) = 0
  rw [hz, map_zero]

/-- The interpolated correction solves every complete order for the same ambient coefficient. -/
theorem completeQuotient_prescribed_correction_all_orders
    (t : invariantCoordinates β) (a : Γ(U.toScheme, ⊤)) (ha : (b).appTop a = t.val)
    (k : ℕ) (z : Γ(completeQuotientFrame e I o U hU k, ⊤))
    (hz : (pullback.fst (j k) i).appTop z = 0)
    (v : invariantCoordinates (α k)) (hv : coeff a k - z = v.val) :
    ∃ z' : Γ(U.toScheme, ⊤), (b).appTop z' = 0 ∧ coeff z' k = z ∧
      ∀ r : ℕ,
        (pullback.fst (j r) i).appTop (coeff z' r) = 0 ∧
        (SourceRestriction.fst (j r) (j r)).appTop (coeff z' r) -
          (SourceRestriction.snd (j r) (j r)).appTop (coeff z' r) =
        (SourceRestriction.fst (j r) (j r)).appTop (coeff a r) -
          (SourceRestriction.snd (j r) (j r)).appTop (coeff a r) := by
  obtain ⟨z', hz', he, v', hv'⟩ := completeQuotient_prescribed_correction_lift
    e I o U hU i τ hi t a ha k z hz v hv
  exact ⟨z', hz', he, fun r ↦
    ⟨completeQuotientCoefficient_boundary_zero e I o U hU i z' hz' r,
      completeQuotientCoefficient_correction e I o U hU a z' v' hv' r⟩⟩

end FLT.Mazur.EquivalenceRelationNormalizedFrames

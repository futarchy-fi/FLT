/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationAmbientBoundaryCorrection
public import FLT.Mazur.EquivalenceRelationCompleteQuotientTower

/-!
# Compatible complete-stage corrections from one ambient coefficient

An invariant boundary value on the original affine chart has one ambient
boundary-zero correction. Its restrictions are exact corrections at all
complete-orbit quotient orders, and commute with every order transition.
This constructs compatibility for boundary values supplied on the ambient
chart; it does not assert that arbitrary formal boundary values extend there.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient SourceRestriction
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
local notation "j" k => completeQuotientFrameInclusion e I o U hU k
local notation "π" k => pullback.fst (quotientMap ρ) (completeQuotientStageMap e I o U hU k)

/-- Restrict one actual ambient coefficient to the full quotient frame cover. -/
def completeQuotientCoefficient (a : Γ(U.toScheme, ⊤)) (k : ℕ) :
    Γ(completeQuotientFrame e I o U hU k, ⊤) := (π k).appTop a

/-- All coefficient orders commute with the constructed scheme transitions. -/
theorem completeQuotientCoefficient_transition (a : Γ(U.toScheme, ⊤))
    {m n : ℕ} (h : m ≤ n) :
    (completeQuotientFrameTransition e I o U hU h).appTop
      (completeQuotientCoefficient e I o U hU a n) =
        completeQuotientCoefficient e I o U hU a m := by
  change ((π n).appTop ≫ (completeQuotientFrameTransition e I o U hU h).appTop) a = _
  rw [← Scheme.Hom.comp_appTop, completeQuotientFrameTransition_fst]
  rfl

/-- The boundary on a complete stage maps to the unchanged ambient original boundary. -/
def completeQuotientBoundaryToAmbient {B : Scheme} (i : B ⟶ source p q I o) (k : ℕ) :
    pullback (j k) i ⟶ pullback U.ι i :=
  pullback.lift (pullback.fst (j k) i ≫ π k) (pullback.snd (j k) i) (by
    rw [Category.assoc]
    exact pullback.condition)

/-- Every ambient boundary-zero coefficient remains exactly boundary-zero at every order. -/
theorem completeQuotientCoefficient_boundary_zero {B : Scheme}
    (i : B ⟶ source p q I o) (z : Γ(U.toScheme, ⊤))
    (hz : (pullback.fst U.ι i).appTop z = 0) (k : ℕ) :
    (pullback.fst (j k) i).appTop (completeQuotientCoefficient e I o U hU z k) = 0 := by
  have he : completeQuotientBoundaryToAmbient e I o U hU i k ≫ pullback.fst U.ι i =
      pullback.fst (j k) i ≫ π k := pullback.lift_fst _ _ _
  have h := congrArg (fun a ↦ (completeQuotientBoundaryToAmbient e I o U hU i k).appTop a) hz
  rw [map_zero] at h
  change ((pullback.fst U.ι i).appTop ≫
    (completeQuotientBoundaryToAmbient e I o U hU i k).appTop) z = 0 at h
  rw [← Scheme.Hom.comp_appTop, he] at h
  exact h

/-- The same ambient invariant difference equalizes on every full original stage relation. -/
theorem completeQuotientCoefficient_correction (a z : Γ(U.toScheme, ⊤))
    (v : invariantCoordinates ρ) (hv : a - z = v.val) (k : ℕ) :
    (SourceRestriction.fst (j k) (j k)).appTop (completeQuotientCoefficient e I o U hU z k) -
      (SourceRestriction.snd (j k) (j k)).appTop (completeQuotientCoefficient e I o U hU z k) =
    (SourceRestriction.fst (j k) (j k)).appTop (completeQuotientCoefficient e I o U hU a k) -
      (SourceRestriction.snd (j k) (j k)).appTop
        (completeQuotientCoefficient e I o U hU a k) := by
  have he := ambient_correction_complete_test e I o U.ι ρ hj a z v hv
    (original (j k) (j k))
    (SourceRestriction.fst (j k) (j k) ≫ π k)
    (SourceRestriction.snd (j k) (j k) ≫ π k)
    (by rw [Category.assoc, original_first]; rfl)
    (by rw [Category.assoc, original_second]; rfl)
    (original_complete_support (j k) (j k) (completeQuotientFrame_complete e I o U hU k))
  simpa only [completeQuotientCoefficient, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply] using he

variable {B : Scheme} (i : B ⟶ source p q I o) [IsClosedImmersion i]
  (τ : Equiv.Perm I →* Aut B)
  (hi : ∀ g, (τ g).hom ≫ i = i ≫ (action e I o g).hom)
local notation "β" => FiniteGroupEquivariantPullback.action ρ τ (action e I o) U.ι i hj hi

/-- One ambient correction yields an exact compatible family at every positive order. -/
theorem exists_compatible_completeQuotient_correction
    (t : invariantCoordinates β) (a : Γ(U.toScheme, ⊤))
    (ha : (pullback.fst U.ι i).appTop a = t.val) :
    ∃ z : Γ(U.toScheme, ⊤), (pullback.fst U.ι i).appTop z = 0 ∧
      ∀ k : ℕ,
        (pullback.fst (j k) i).appTop (completeQuotientCoefficient e I o U hU z k) = 0 ∧
        (SourceRestriction.fst (j k) (j k)).appTop
            (completeQuotientCoefficient e I o U hU z k) -
          (SourceRestriction.snd (j k) (j k)).appTop
            (completeQuotientCoefficient e I o U hU z k) =
        (SourceRestriction.fst (j k) (j k)).appTop
            (completeQuotientCoefficient e I o U hU a k) -
          (SourceRestriction.snd (j k) (j k)).appTop
            (completeQuotientCoefficient e I o U hU a k) := by
  obtain ⟨z, hz, v, hv⟩ := exists_ambient_boundary_correction e I o U.ι ρ hj i τ hi t a ha
  exact ⟨z, hz, fun k ↦ ⟨completeQuotientCoefficient_boundary_zero e I o U hU i z hz k,
    completeQuotientCoefficient_correction e I o U hU a z v hv k⟩⟩

end FLT.Mazur.EquivalenceRelationNormalizedFrames

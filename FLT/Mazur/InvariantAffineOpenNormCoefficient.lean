/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFlatRelationNormCoefficient
public import FLT.Mazur.InvariantOpenCoefficientRestriction
public import FLT.Mazur.EquivalenceRelationInvariantRestriction

/-!
# Norm coefficients on actual invariant affine opens

These coefficients use the whole restricted relation. Restriction between
nested affine invariant domains preserves the norm, even when the ambient
source is not affine.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.InvariantAffineOpenNormCoefficient
open InvariantOpenCoefficientRestriction
set_option backward.isDefEq.respectTransparency false
variable {D X : Scheme.{0}} (p q : D ⟶ X)
  [IsFinite p] [Flat p] [LocallyOfFinitePresentation p]
  (e : CategoryTheory.EquivalenceRelation p q)
  (U : X.Opens) (hU : p ⁻¹ᵁ U = q ⁻¹ᵁ U) (haU : IsAffineOpen U)
local notation "r" => p.resLE U _ le_rfl
local notation "s" => q.resLE U _ hU.le

omit [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] in
/-- The full first-endpoint square of an invariant open. -/
theorem first_isPullback : IsPullback (p ⁻¹ᵁ U).ι r p U.ι := by
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  exact (isPullback_morphismRestrict p U).flip

/-- The constructed invariant norm on an affine open of the original source. -/
def coefficient (a : Γ(X, ⊤)) : coefficients p q U hU := by
  let _ : IsAffine U.toScheme := haU
  let _ : IsFinite r := by rw [Scheme.Hom.resLE_eq_morphismRestrict]; infer_instance
  let _ : IsAffine (p ⁻¹ᵁ U).toScheme := isAffine_of_isAffineHom r
  let er := EquivalenceRelationFiber.invariantRestrictionEquivalence e
    (first_isPullback p U) (Scheme.Hom.resLE_comp_ι q hU.le).symm
  exact FiniteFlatRelationNormCoefficient.coefficient r s er (U.ι.appTop a)

/-- Local norm nonvanishing is the whole original orbit condition. -/
theorem mem_basicOpen_coefficient (a : Γ(X, ⊤)) (x : U.toScheme) :
    x ∈ U.toScheme.basicOpen (coefficient p q e U hU haU a).val ↔
      ∀ z : D, p z = U.ι x → q z ∈ X.basicOpen a := by
  let _ : IsAffine U.toScheme := haU
  let _ : IsFinite r := by rw [Scheme.Hom.resLE_eq_morphismRestrict]; infer_instance
  let _ : IsAffine (p ⁻¹ᵁ U).toScheme := isAffine_of_isAffineHom r
  rw [coefficient, FiniteFlatRelationNormCoefficient.mem_basicOpen_coefficient]
  have hp := first_isPullback p U
  constructor
  · intro h z hz
    obtain ⟨w, hw, hx⟩ := Scheme.exists_preimage_of_isPullback hp z x hz
    have he : U.ι (s w) = q z :=
      (congrArg (fun f ↦ f w) (Scheme.Hom.resLE_comp_ι q hU.le)).trans (congrArg q hw)
    have ht := h w hx
    rw [← Scheme.preimage_basicOpen_top] at ht
    exact he ▸ ht
  · intro h w hw
    rw [← Scheme.preimage_basicOpen_top]
    have he : p ((p ⁻¹ᵁ U).ι w) = U.ι x :=
      (congrArg (fun f ↦ f w) hp.w).trans (congrArg U.ι hw)
    have ht := h _ he
    change U.ι (s w) ∈ X.basicOpen a
    have hs : U.ι (s w) = q ((p ⁻¹ᵁ U).ι w) :=
      congrArg (fun f ↦ f w) (Scheme.Hom.resLE_comp_ι q hU.le)
    exact hs.symm ▸ ht

variable (V : X.Opens) (hV : p ⁻¹ᵁ V = q ⁻¹ᵁ V) (haV : IsAffineOpen V) (h : V ≤ U)

/-- Nested actual affine domains compute precisely the same restricted norm. -/
theorem coefficient_restrict (a : Γ(X, ⊤)) :
    restriction p q U V hU hV h (coefficient p q e U hU haU a) =
      coefficient p q e V hV haV a := by
  let _ : IsAffine U.toScheme := haU
  let _ : IsAffine V.toScheme := haV
  let _ : IsFinite r := by rw [Scheme.Hom.resLE_eq_morphismRestrict]; infer_instance
  let _ : IsFinite (p.resLE V _ le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]; infer_instance
  let _ : IsAffine (p ⁻¹ᵁ U).toScheme := isAffine_of_isAffineHom r
  let _ : IsAffine (p ⁻¹ᵁ V).toScheme := isAffine_of_isAffineHom (p.resLE V _ le_rfl)
  let g := D.homOfLE (p.preimage_mono h)
  have hp : g ≫ r = p.resLE V _ le_rfl ≫ X.homOfLE h := by
    apply (cancel_mono U.ι).mp
    simp only [Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.homOfLE_ι,
      Scheme.homOfLE_ι_assoc, g]
  have hq : g ≫ s = q.resLE V _ hV.le ≫ X.homOfLE h := by
    apply (cancel_mono U.ι).mp
    simp only [Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.homOfLE_ι,
      Scheme.homOfLE_ι_assoc, g]
  have H : IsPullback g (p.resLE V _ le_rfl) r (X.homOfLE h) := by
    apply IsPullback.of_right _ hp (first_isPullback p U)
    simpa only [g, Scheme.homOfLE_ι] using first_isPullback p V
  apply Subtype.ext
  change (X.homOfLE h).appTop _ = _
  let eU := EquivalenceRelationFiber.invariantRestrictionEquivalence e
    (first_isPullback p U) (Scheme.Hom.resLE_comp_ι q hU.le).symm
  let eV := EquivalenceRelationFiber.invariantRestrictionEquivalence e
    (first_isPullback p V) (Scheme.Hom.resLE_comp_ι q hV.le).symm
  have he := FiniteFlatRelationNormCoefficient.coefficient_baseChange _ _ eU _ _ eV _ _ H hq
    (U.ι.appTop a)
  have hs : (X.homOfLE h).appTop (U.ι.appTop a) = V.ι.appTop a := by
    change (X.homOfLE h ≫ U.ι).appTop a = _
    rw [Scheme.homOfLE_ι]
  rw [hs] at he
  exact he.symm

end FLT.Mazur.InvariantAffineOpenNormCoefficient

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationOpenFunctionDescent

/-!
# Invariant open-section rings in the original scheme coordinates

Transport the restricted-scheme descent comparison through the canonical
open-subscheme section isomorphisms. The resulting map is the original
structure-sheaf pullback, including the required domain identifications.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeEffectiveEpiSections
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X A : Scheme.{u}} (p q : A ⟶ X) (W : X.Opens) (hW : p ⁻¹ᵁ W = q ⁻¹ᵁ W)

/-- Invariant regular functions on an actual open of the original source scheme. -/
def relationOpenFunctions : Subring Γ(X, W) :=
  RingHom.eqLocus (p.app W).hom (q.appLE W (p ⁻¹ᵁ W) hW.le).hom

/-- The restricted global relation equation is exactly the original open-section equation. -/
theorem relationOpenFunctions_iff (s : Γ(X, W)) :
    W.topIso.inv s ∈
        compatibleFunctions (p.resLE W (p ⁻¹ᵁ W) le_rfl) (q.resLE W (p ⁻¹ᵁ W) hW.le) ↔
      s ∈ relationOpenFunctions p q W hW := by
  change (p.resLE W (p ⁻¹ᵁ W) le_rfl).appTop (W.topIso.inv s) =
    (q.resLE W (p ⁻¹ᵁ W) hW.le).appTop (W.topIso.inv s) ↔ _
  simp only [resLE_appTop_coordinates, ConcreteCategory.comp_apply, Iso.inv_hom_id_apply,
    Scheme.Hom.appLE_eq_app]
  exact (p ⁻¹ᵁ W).topIso.symm.commRingCatIsoToRingEquiv.injective.eq_iff

/-- Original open invariants are the same ring as the actual restricted-scheme invariants. -/
def relationOpenCoordinates : relationOpenFunctions p q W hW ≃+*
    compatibleFunctions (p.resLE W (p ⁻¹ᵁ W) le_rfl) (q.resLE W (p ⁻¹ᵁ W) hW.le) := by
  let φ := (W.topIso.inv.hom.comp (relationOpenFunctions p q W hW).subtype).codRestrict _
    (fun s ↦ (relationOpenFunctions_iff p q W hW s.val).mpr s.property)
  apply RingEquiv.ofBijective φ
  constructor
  · intro s t h
    exact Subtype.ext (W.topIso.symm.commRingCatIsoToRingEquiv.injective
      (congrArg Subtype.val h))
  · intro s
    have hs : W.topIso.hom s.val ∈ relationOpenFunctions p q W hW := by
      apply (relationOpenFunctions_iff p q W hW _).mp
      simpa only [Iso.hom_inv_id_apply] using s.property
    exact ⟨⟨W.topIso.hom s.val, hs⟩, Subtype.ext (Iso.hom_inv_id_apply W.topIso s.val)⟩

variable {Y B K : Scheme.{u}} {a b : B ⟶ Y}
  (g : Y ⟶ X) (k : B ⟶ A) (h₁ : k ≫ p = a ≫ g) (h₂ : k ≫ q = b ≫ g)
  {r t : K ⟶ Y} (H : IsPullback r t g g)
  (l : K ⟶ B) (hl₁ : l ≫ a = r) (hl₂ : l ≫ b = t)
  [Flat g] [Surjective g] [LocallyOfFinitePresentation g]
  [Flat k] [Surjective k] [LocallyOfFinitePresentation k]

/-- Descent identifies both actual open invariant rings in their original section coordinates. -/
def relationOpenInvariantRingEquiv : relationOpenFunctions p q W hW ≃+*
    relationOpenFunctions a b (g ⁻¹ᵁ W) (relationSource_preimage g k h₁ h₂ W hW) :=
  (relationOpenCoordinates p q W hW).trans
    ((relationOpenFunctionRingEquiv g k h₁ h₂ W hW H l hl₁ hl₂).trans
      (relationOpenCoordinates a b _ _).symm)

/-- The comparison is the original pullback on open sections. -/
theorem relationOpenInvariantRingEquiv_val (s : relationOpenFunctions p q W hW) :
    (relationOpenInvariantRingEquiv p q W hW g k h₁ h₂ H l hl₁ hl₂ s).val =
      g.app W s.val := by
  apply (g ⁻¹ᵁ W).topIso.symm.commRingCatIsoToRingEquiv.injective
  change ((relationOpenCoordinates a b _ _)
    ((relationOpenInvariantRingEquiv p q W hW g k h₁ h₂ H l hl₁ hl₂) s)).val = _
  dsimp only [relationOpenInvariantRingEquiv, RingEquiv.trans_apply]
  rw [RingEquiv.apply_symm_apply]
  change (g ∣_ W).appTop (W.topIso.inv s.val) = _
  rw [← Scheme.Hom.resLE_eq_morphismRestrict, resLE_appTop_coordinates]
  simp only [Scheme.Hom.appLE_eq_app, ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
  rfl

end FLT.Mazur.SchemeEffectiveEpiSections

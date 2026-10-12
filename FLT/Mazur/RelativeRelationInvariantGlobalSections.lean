/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationInvariantSectionRings
public import FLT.Mazur.SchemeEffectiveEpiSections

/-!
# Invariant functions in original open and global section coordinates

The open-subscheme section isomorphism preserves exactly the two original
endpoint equations. Its restriction is a ring equivalence of invariant functions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace FLT.Mazur.RelativeRelationOrbit
open SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{u}} {A U : Over S} {p q : A ⟶ U}
  (V : U.left.Opens) (hV : p.left ⁻¹ᵁ V = q.left ⁻¹ᵁ V)

/-- The global equation is exactly the original equation after the open-section isomorphism. -/
theorem originalInvariant_global_iff (s : Γ(U.left, V)) :
    V.topIso.inv s ∈ compatibleFunctions (p.left.resLE V _ le_rfl)
      (q.left.resLE V _ hV.le) ↔ s ∈ originalInvariantSections V hV := by
  change (p.left.resLE V _ le_rfl).appTop (V.topIso.inv s) =
    (q.left.resLE V _ hV.le).appTop (V.topIso.inv s) ↔
      p.left.app V s = q.left.appLE V (p.left ⁻¹ᵁ V) hV.le s
  simp only [Scheme.Hom.resLE_app_top, Scheme.Hom.appLE_eq_app,
    ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
  exact (p.left ⁻¹ᵁ V).topIso.symm.commRingCatIsoToRingEquiv.injective.eq_iff

/-- The original invariant section ring in global coordinates on its actual open scheme. -/
def originalInvariantGlobalEquiv : originalInvariantSections V hV ≃+*
    compatibleFunctions (p.left.resLE V _ le_rfl) (q.left.resLE V _ hV.le) := by
  let φ := (V.topIso.inv.hom.comp (originalInvariantSections V hV).subtype).codRestrict
    (compatibleFunctions (p.left.resLE V _ le_rfl) (q.left.resLE V _ hV.le))
    (fun s ↦ (originalInvariant_global_iff V hV s.val).mpr s.property)
  apply RingEquiv.ofBijective φ
  constructor
  · intro s t h
    exact Subtype.ext (V.topIso.symm.commRingCatIsoToRingEquiv.injective
      (congrArg Subtype.val h))
  · intro t
    have ht : V.topIso.hom t.val ∈ originalInvariantSections V hV := by
      apply (originalInvariant_global_iff V hV _).mp
      simpa only [Iso.hom_inv_id_apply] using t.property
    exact ⟨⟨V.topIso.hom t.val, ht⟩, Subtype.ext (V.topIso.hom_inv_id_apply t.val)⟩

/-- The equivalence is the original open-section isomorphism. -/
theorem originalInvariantGlobalEquiv_val (s : originalInvariantSections V hV) :
    (originalInvariantGlobalEquiv V hV s).val = V.topIso.inv s.val := rfl

/-- Restriction between open subschemes uses the original presheaf restriction maps. -/
theorem homOfLE_appTop_coordinates {B C : U.left.Opens} (h : B ≤ C)
    (s : Γ(U.left, C)) :
    (Scheme.homOfLE _ h).appTop (C.topIso.inv s) =
      B.topIso.inv (U.left.presheaf.map (homOfLE h).op s) := by
  have hn := U.left.restrictFunctorΓ.inv.naturality (homOfLE h).op
  exact congrArg (fun k ↦ k s) hn.symm

end FLT.Mazur.RelativeRelationOrbit

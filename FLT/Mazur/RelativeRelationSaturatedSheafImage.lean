/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationInvariantGlobalSections
public import FLT.Mazur.RelativeRelationSaturationFunctionDescent
public import FLT.Mazur.RelativeRelationSaturatedSections

/-!
# The exact image of original invariant-sheaf sections on a generator

The original sheaf's section ring is the full original relation's compatible
function ring on the generating open. The comparison is the previously constructed
restriction embedding, now with its image characterized in both directions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace FLT.Mazur.RelativeRelationOrbit
open SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{u}} {A U : Over S} {p q : A ⟶ U}
  (e : CategoryTheory.EquivalenceRelation p q) (hq : IsOpenMap q.left)
  (W : U.left.Opens) [Etale q.left]
local notation "r" => SchemeRelationRestriction.fst p.left q.left W.ι
local notation "s" => SchemeRelationRestriction.snd p.left q.left W.ι

/-- Sections of the original invariant sheaf are exactly full-relation compatible functions. -/
def saturatedSheafFunctionEquiv :
    (invariantSheaf e).obj.obj (op (orbitImageOpen e hq W)) ≃+* compatibleFunctions r s :=
  ((invariantSectionRingEquiv e (orbitImageOpen e hq W)).trans
    (originalInvariantGlobalEquiv (saturateOpen e hq W).val
      (saturateOpen_preimage_eq e hq W))).trans (saturationFunctionRingEquiv e hq W)

/-- The equivalence is the original sheaf restriction, with only the open-section coordinates. -/
theorem saturatedSheafFunctionEquiv_val
    (t : (invariantSheaf e).obj.obj (op (orbitImageOpen e hq W))) :
    (saturatedSheafFunctionEquiv e hq W t).val =
      W.topIso.inv (saturatedSheafRestriction e hq W t) := by
  change (Scheme.homOfLE _ (le_saturateOpen e hq W)).appTop
    ((saturateOpen e hq W).val.topIso.inv
      ((invariantInclusion e).hom.app (op (orbitImageOpen e hq W)) t)) = _
  rw [homOfLE_appTop_coordinates]
  rfl

/-- The embedding's image consists precisely of functions compatible on the original relation. -/
theorem saturatedSheafRestriction_exists_iff (v : Γ(U.left, W)) :
    (∃ t, saturatedSheafRestriction e hq W t = v) ↔
      W.topIso.inv v ∈ compatibleFunctions r s := by
  constructor
  · rintro ⟨t, rfl⟩
    rw [← saturatedSheafFunctionEquiv_val]
    exact (saturatedSheafFunctionEquiv e hq W t).property
  · intro hv
    let t := (saturatedSheafFunctionEquiv e hq W).symm ⟨W.topIso.inv v, hv⟩
    refine ⟨t, W.topIso.symm.commRingCatIsoToRingEquiv.injective ?_⟩
    change W.topIso.inv (saturatedSheafRestriction e hq W t) = W.topIso.inv v
    rw [← saturatedSheafFunctionEquiv_val]
    exact congrArg Subtype.val ((saturatedSheafFunctionEquiv e hq W).apply_symm_apply _)

/-- Every original compatible function comes from a unique section of the original sheaf. -/
theorem saturatedSheafRestriction_existsUnique (v : Γ(U.left, W))
    (hv : W.topIso.inv v ∈ compatibleFunctions r s) :
    ∃! t, saturatedSheafRestriction e hq W t = v := by
  obtain ⟨t, ht⟩ := (saturatedSheafRestriction_exists_iff e hq W v).mpr hv
  exact ⟨t, ht, fun z hz ↦ saturatedSheafRestriction_injective e hq W (hz.trans ht.symm)⟩

end FLT.Mazur.RelativeRelationOrbit

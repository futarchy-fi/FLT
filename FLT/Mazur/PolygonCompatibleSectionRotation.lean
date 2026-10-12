/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonBoundarySectionRotation
public import FLT.Mazur.PolygonCompatibleHomogeneousSections

/-!
# Rotation of the actual compatible boundary sections

The canonical stage rotations assemble on the original ring of compatible
sections. Their identity, composition and inverse laws are detected by the
original stage evaluations, and every homogeneous degree is preserved.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R : Type) [CommRing R] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Assemble the actual cyclic pullbacks in the original compatible-section ring. -/
def compatibleSectionRingRotation (a : ZMod n) :
    compatibleSectionRing R n h →+* compatibleSectionRing R n h :=
  compatibleSectionLift R n h
    (fun m ↦ (boundarySectionsRotation R n h m a).comp (compatibleSectionEval R n h m))
    (by
      intro k l f
      rw [← RingHom.comp_assoc, boundarySectionsRotation_naturality,
        RingHom.comp_assoc, compatibleSectionEval_transition])

attribute [local semireducible] CompatibleSections

/-- The constructed rotation on the named compatible-section carrier. -/
def compatibleSectionRotation (a : ZMod n) :
    CompatibleSections R n h →+* CompatibleSections R n h :=
  compatibleSectionRingRotation R n h a

/-- Every original stage evaluation detects its actual canonical cyclic pullback. -/
theorem compatibleSectionRotation_eval (a : ZMod n) (m : ℕ) (s : CompatibleSections R n h) :
    compatibleEval R n h m (compatibleSectionRotation R n h a s) =
      boundarySectionsRotation R n h m a (compatibleEval R n h m s) := rfl

/-- Rotation preserves the actual homogeneous degree at all orders simultaneously. -/
theorem compatibleSectionRotation_degree (a : ZMod n) (d : ℕ) {s : CompatibleSections R n h}
    (hs : IsCompatibleDegree R n h d s) :
    IsCompatibleDegree R n h d (compatibleSectionRotation R n h a s) := by
  intro m
  rw [compatibleSectionRotation_eval]
  exact boundarySectionsRotation_mem_grade R n h m a d (hs m)

/-- Zero rotation fixes every compatible section. -/
@[simp] theorem compatibleSectionRotation_zero :
    compatibleSectionRotation R n h 0 = RingHom.id _ := by
  apply RingHom.ext
  intro s
  apply compatibleEval_ext R n h
  intro m
  rw [compatibleSectionRotation_eval, boundarySectionsRotation_zero]
  rfl

/-- The original label addition acts by composition on the compatible section ring. -/
theorem compatibleSectionRotation_add (a b : ZMod n) :
    compatibleSectionRotation R n h (a + b) =
      (compatibleSectionRotation R n h a).comp (compatibleSectionRotation R n h b) := by
  apply RingHom.ext
  intro s
  apply compatibleEval_ext R n h
  intro m
  simp only [RingHom.comp_apply, compatibleSectionRotation_eval, boundarySectionsRotation_add]

/-- Every constructed rotation is an automorphism of the actual compatible section ring. -/
def compatibleSectionRotationEquiv (a : ZMod n) :
    CompatibleSections R n h ≃+* CompatibleSections R n h :=
  RingEquiv.ofRingHom (compatibleSectionRotation R n h a)
    (compatibleSectionRotation R n h (-a))
    (by rw [← compatibleSectionRotation_add, add_neg_cancel, compatibleSectionRotation_zero])
    (by rw [← compatibleSectionRotation_add, neg_add_cancel, compatibleSectionRotation_zero])

end FLT.Mazur.PolygonInfinitesimalStages

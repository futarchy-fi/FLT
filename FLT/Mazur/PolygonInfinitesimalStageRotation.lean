/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalRotationBaseChange
public import FLT.Mazur.PolygonInfinitesimalSystem

/-!
# The cyclic action on the original compatible stage system

The actual rotations commute with the specified adjacent restrictions, so they
assemble to natural automorphisms of the entire original scheme system. They
preserve the arithmetic structure and rotate the original marked sections.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal PolygonPinching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R : Type u) [CommRing R] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The actual chart rotation at the specified truncated coefficient stage. -/
def stageRotation (m : ℕ) (a : ZMod n) :
    (family R m n h).left ⟶ (family R m n h).left :=
  rotation (Ring R m) (parameter R m) n h a

/-- The actual adjacent coefficient restriction commutes with rotation. -/
@[reassoc] theorem stageRotation_restriction (m : ℕ) (a : ZMod n) :
    stageRotation R n h m a ≫ stageRestriction R m n h =
      stageRestriction R m n h ≫ stageRotation R n h (m + 1) a :=
  rotation_parameterProjection (restriction R m).toRingHom _ _ (restriction_parameter R m) n h a

/-- The constructed rotation is natural across every transition of the original system. -/
def systemRotation (a : ZMod n) : stageSystem R n h ⟶ stageSystem R n h :=
  NatTrans.ofSequence (fun m ↦ stageRotation R n h m a) (by
    intro m
    simpa only [stageSystem, Functor.ofSequence_obj, Functor.ofSequence_map_homOfLE_succ]
      using (stageRotation_restriction R n h m a).symm)

/-- Evaluation of the natural action is the actual chart rotation. -/
theorem systemRotation_app (a : ZMod n) (m : ℕ) :
    (systemRotation R n h a).app m = stageRotation R n h m a := rfl

/-- The whole-system rotation preserves the specified arithmetic bases. -/
theorem systemRotation_structure (a : ZMod n) :
    systemRotation R n h a ≫ systemStructure R n h = systemStructure R n h := by
  ext m
  exact rotation_toBase (Ring R m) (parameter R m) n h a

/-- Rotation carries the complete original marked section system to its translated label. -/
theorem systemMarking_rotation (a : ZMod n) (i : Fin n) :
    systemMarking R n h i ≫ systemRotation R n h a =
      systemMarking R n h (rotateIndex a i) := by
  ext m
  exact marking_rotation (Ring R m) (parameter R m) n h a i 1

/-- Zero acts as the identity on the entire stage system. -/
@[simp] theorem systemRotation_zero : systemRotation R n h 0 = 𝟙 _ := by
  ext m
  exact rotation_zero (Ring R m) (parameter R m) n h

/-- The original label addition gives composition on the entire stage system. -/
theorem systemRotation_add (a b : ZMod n) :
    systemRotation R n h (a + b) = systemRotation R n h a ≫ systemRotation R n h b := by
  ext m
  exact rotation_add (Ring R m) (parameter R m) n h a b

/-- Each cyclic translation is a natural automorphism of the original infinitesimal system. -/
def systemRotationIso (a : ZMod n) : stageSystem R n h ≅ stageSystem R n h where
  hom := systemRotation R n h a
  inv := systemRotation R n h (-a)
  hom_inv_id := by rw [← systemRotation_add, add_neg_cancel, systemRotation_zero]
  inv_hom_id := by rw [← systemRotation_add, neg_add_cancel, systemRotation_zero]

end FLT.Mazur.PolygonInfinitesimalStages

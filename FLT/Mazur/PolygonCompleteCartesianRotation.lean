/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteCartesianMarkings
public import FLT.Mazur.PolygonCompleteMarkingRotation

/-!
# The original cyclic action on every specified complete-family square

Pull back the constructed complete automorphism to the given cartesian square.
The result preserves its actual base, action law and all original markings.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonPinching
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase completeRotation

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {S Y : Scheme} (s : S ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ S)
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) s)

/-- Rotation of the original chosen square, constructed by its cartesian property. -/
def completeCartesianRotation (a : ZMod n) : Y ⟶ Y :=
  hs.lift (p ≫ completeRotation K n h a) q
    (by rw [Category.assoc, completeRotation_toBase]; exact hs.w)

/-- The lifted automorphism retains the original total-space action. -/
@[reassoc] theorem completeCartesianRotation_fst (a : ZMod n) :
    completeCartesianRotation K n h s p q hs a ≫ p = p ≫ completeRotation K n h a :=
  hs.lift_fst _ _ _

/-- Rotation preserves the actual specified base projection. -/
@[reassoc] theorem completeCartesianRotation_snd (a : ZMod n) :
    completeCartesianRotation K n h s p q hs a ≫ q = q := hs.lift_snd _ _ _

/-- The identity label acts as the identity on the original chosen fiber. -/
@[simp] theorem completeCartesianRotation_zero :
    completeCartesianRotation K n h s p q hs 0 = 𝟙 Y := by
  apply hs.hom_ext
  · rw [completeCartesianRotation_fst, completeRotation_zero, Category.comp_id, Category.id_comp]
  · rw [completeCartesianRotation_snd, Category.id_comp]

/-- The original cyclic addition law survives on every specified square. -/
theorem completeCartesianRotation_add (a b : ZMod n) :
    completeCartesianRotation K n h s p q hs (a + b) =
      completeCartesianRotation K n h s p q hs a ≫
        completeCartesianRotation K n h s p q hs b := by
  apply hs.hom_ext
  · simp only [Category.assoc, completeCartesianRotation_fst,
      completeCartesianRotation_fst_assoc, completeRotation_add]
  · simp only [Category.assoc, completeCartesianRotation_snd]

/-- The negative label is an actual inverse over the original specified base. -/
def completeCartesianRotationIso (a : ZMod n) : Y ≅ Y where
  hom := completeCartesianRotation K n h s p q hs a
  inv := completeCartesianRotation K n h s p q hs (-a)
  hom_inv_id := by
    rw [← completeCartesianRotation_add, add_neg_cancel, completeCartesianRotation_zero]
  inv_hom_id := by
    rw [← completeCartesianRotation_add, neg_add_cancel, completeCartesianRotation_zero]

/-- The pulled-back cyclic action rotates every original labeled marking. -/
@[reassoc] theorem completeCartesianMarking_rotation (a : ZMod n) (i : Fin n) :
    completeCartesianMarking K n h s p q hs i ≫
        completeCartesianRotation K n h s p q hs a =
      completeCartesianMarking K n h s p q hs (rotateIndex a i) := by
  apply hs.hom_ext
  · rw [Category.assoc, completeCartesianRotation_fst,
      completeCartesianMarking_fst_assoc, completeBaseMarking_rotation,
      completeCartesianMarking_fst]
  · rw [Category.assoc, completeCartesianRotation_snd,
      completeCartesianMarking_snd, completeCartesianMarking_snd]

end FLT.Mazur.PolygonInfinitesimalStages

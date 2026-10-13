/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteCyclicSchemeAction

/-!
# The original finite marking scheme is an actual cyclic orbit

The closed finite etale marking map intertwines the regular constant group
action with both the complete-family action and its smooth restriction.
These equalities retain the complete scheme structures in every characteristic.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase completeRotation
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {S Y : Scheme} (s : S ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ S)
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) s)

/-- The original residue-labeled sections form an orbit under the actual rotations. -/
@[reassoc] theorem completeCyclicSection_rotation (a b : ZMod n) :
    completeCyclicSection K n h s p q hs b ≫
      completeCartesianRotationOver K n h s p q hs a =
        completeCyclicSection K n h s p q hs (a + b) := by
  apply Over.OverMorphism.ext
  simpa only [completeCyclicSection, completeCartesianRotationOver, Over.comp_left,
    Over.homMk_left, PolygonPinching.rotateIndex, RingEquiv.apply_symm_apply, add_comm] using
      completeCartesianMarking_rotation K n h s p q hs a ((ZMod.finEquiv n).symm b)

/-- The whole finite scheme embedding intertwines the regular and complete-family actions. -/
theorem completeCyclicMarking_equivariant :
    μ[ConstantCyclicGroup.model S n] ≫ completeCyclicMarking K n h s p q hs =
      ConstantCyclicGroup.model S n ◁ completeCyclicMarking K n h s p q hs ≫
        completeCyclicAction K n h s p q hs :=
  ConstantCyclicSchemeAction.marking_equivariant _ _
    (completeCyclicSection_rotation K n h s p q hs)

/-- The complete marking scheme is the orbit of its original identity-labeled marking. -/
theorem completeCyclicMarking_identityOrbit :
    (ρ_ (ConstantCyclicGroup.model S n)).inv ≫
      ConstantCyclicGroup.model S n ◁
        (η[ConstantCyclicGroup.model S n] ≫ completeCyclicMarking K n h s p q hs) ≫
          completeCyclicAction K n h s p q hs = completeCyclicMarking K n h s p q hs := by
  rw [whiskerLeft_comp, Category.assoc, ← completeCyclicMarking_equivariant,
    MonObj.mul_one_assoc, Iso.inv_hom_id_assoc]

variable [LocallyOfFinitePresentation q]

/-- The actual smooth finite marking map is equivariant for the entire constant group scheme. -/
theorem completeSmoothCyclicMarking_equivariant :
    μ[ConstantCyclicGroup.model S n] ≫ completeSmoothCyclicMarking K n h s p q hs =
      ConstantCyclicGroup.model S n ◁ completeSmoothCyclicMarking K n h s p q hs ≫
        completeSmoothCyclicAction K n h s p q hs := by
  apply ConstantCyclicSchemeAction.marking_equivariant
  intro a b
  apply Over.OverMorphism.ext
  simpa only [completeSmoothCartesianRotationOver, Over.comp_left, Over.homMk_left,
    PolygonPinching.rotateIndex, RingEquiv.apply_symm_apply, add_comm] using
      completeSmoothCartesianMarking_rotation K n h s p q hs a ((ZMod.finEquiv n).symm b)

/-- The original finite smooth marking scheme is the orbit of its identity section. -/
theorem completeSmoothCyclicMarking_identityOrbit :
    (ρ_ (ConstantCyclicGroup.model S n)).inv ≫
      ConstantCyclicGroup.model S n ◁
        (η[ConstantCyclicGroup.model S n] ≫ completeSmoothCyclicMarking K n h s p q hs) ≫
          completeSmoothCyclicAction K n h s p q hs =
            completeSmoothCyclicMarking K n h s p q hs := by
  rw [whiskerLeft_comp, Category.assoc, ← completeSmoothCyclicMarking_equivariant,
    MonObj.mul_one_assoc, Iso.inv_hom_id_assoc]

end FLT.Mazur.PolygonInfinitesimalStages

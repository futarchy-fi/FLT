/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomRelabelCurve
public import FLT.Mazur.OddWeierstrassCyclicHomAffineMarkings

/-!
# The full odd-chart comparison retains both independent markings

The auxiliary marking is realized on every test scheme. Relabeling carries
all of its sections to their prescribed labels on the original full curve.
On affine tests these are exactly the previously constructed markings.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.OddWeierstrassParameter
open AuxiliaryLevel
open UniversalWeierstrass (Labels)
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme}
  (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)

/-- The auxiliary labels on the entire source curve over any test scheme. -/
def cyclicHomFullAuxiliaryMarking : Labels 3 →*
    (𝟙_ (Over T) ⟶ (cyclicHomSourceCurve n f).group) :=
  GroupMarkingBaseChange.marking (cyclicHomAuxiliaryPoint n f ≫ levelThree.hom)
    universalGroup _ (markingOf universalGroup (Labels 3)
      (Over.homMk (cyclicHomAuxiliaryPoint n f) (by simp) ≫ levelThreeInclusion))

/-- Projection to the universal group retains each original auxiliary label. -/
@[reassoc] theorem cyclicHomFullAuxiliaryMarking_fst (i : Labels 3) :
    (cyclicHomFullAuxiliaryMarking n f i).left ≫
      pullback.fst universalGroup.hom (cyclicHomAuxiliaryPoint n f ≫ levelThree.hom) =
        cyclicHomAuxiliaryPoint n f ≫ (levelThreeMarking i).left := by
  have h := GroupMarkingBaseChange.marking_fst
    (cyclicHomAuxiliaryPoint n f ≫ levelThree.hom) universalGroup (𝟙_ (Over T))
    (markingOf universalGroup (Labels 3)
      (Over.homMk (cyclicHomAuxiliaryPoint n f) (by simp) ≫ levelThreeInclusion)) i
  exact h.trans (by
    change (cyclicHomAuxiliaryPoint n f ≫ levelThreeInclusion.left) ≫
      (value universalGroup (Labels 3) i).left = _
    rw [Category.assoc]
    rfl)

/-- The universal faithful action permutes the actual level-three sections. -/
@[reassoc] theorem levelThreeAction_mark (a : MulAut (Labels 3)) (i : Labels 3) :
    (levelThreeAction a).hom ≫ (levelThreeMarking i).left =
      (levelThreeMarking (a.symm i)).left := by
  change (faithfulAction universalGroup (Labels 3) a).hom ≫
    (faithfulInclusion universalGroup (Labels 3)).left ≫
      (value universalGroup (Labels 3) i).left = _
  rw [← Category.assoc, faithfulAction_inclusion, Category.assoc]
  have h := congrArg Over.Hom.left (relabelAction_value universalGroup a i)
  change (relabelSchemeAction universalGroup a).hom ≫
    (value universalGroup (Labels 3) i).left = _ at h
  rw [h]
  rfl

variable (a : MulAut (Labels 3)) (c : MulAut (Multiplicative (ZMod n)))
local notation "fR" => f ≫ Over.Hom.left (cyclicHomRelabel n a c)

/-- The relabeled parameter has exactly the original relabeled auxiliary coordinate. -/
theorem cyclicHomRelabel_auxiliaryPoint :
    cyclicHomAuxiliaryPoint n fR =
      cyclicHomAuxiliaryPoint n f ≫ (levelThreeAction a).hom := by
  have h := congrArg (fun z ↦ f ≫ z.left) (cyclicHomRelabel_auxiliary n a c)
  exact (Category.assoc _ _ _).trans h

/-- Every auxiliary label is retained by the same full curve comparison as the cyclic marking. -/
theorem cyclicHomRelabelCurveIso_auxiliary (i : Labels 3) :
    cyclicHomFullAuxiliaryMarking n fR i ≫ (cyclicHomRelabelCurveIso n a c f).hom.group =
      cyclicHomFullAuxiliaryMarking n f (a.symm i) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [Over.comp_left, Category.assoc, cyclicHomRelabelCurveIso_fst,
      cyclicHomFullAuxiliaryMarking_fst, cyclicHomFullAuxiliaryMarking_fst,
      cyclicHomRelabel_auxiliaryPoint, Category.assoc, levelThreeAction_mark]
  · exact Over.w _ |>.trans (Over.w _).symm

/-- On affine tests the full auxiliary marking is the original affine construction. -/
theorem cyclicHomFullAuxiliaryMarking_affine {R : Type} [CommRing R]
    (g : Spec (.of R) ⟶ (cyclicHomAuxiliaryScheme n).left) :
    cyclicHomFullAuxiliaryMarking n g = cyclicHomSourceAuxiliaryMarking n g := rfl

end FLT.Mazur.OddWeierstrassParameter

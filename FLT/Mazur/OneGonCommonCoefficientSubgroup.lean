/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CharacterCommonCoefficientGroup
public import FLT.Mazur.OneGonCommonCoefficientInclusion

/-!
# Independent subgroup maps in the whole one-gon

An equality of whole-cubic embeddings forces equality of their smooth factors
under the actual common-base group comparison. Character sources retain their
canonical comparison, including when the subgroup is nonreduced.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Obj
namespace FLT.Mazur.OneGonSmoothing
open WeierstrassIntegralChart WeierstrassDividedDepth CharacterSchemeBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A C] [Algebra B C] (a : A) (b : B)
  (h : algebraMap A C a = algebraMap B C b)

instance smoothCurveInclusion_mono : Mono (smoothCurveInclusion b) := by
  let _ : Mono (smoothCurveInclusion b).left :=
    inferInstanceAs (Mono (integralSmoothOpen (equation b)).ι)
  exact Over.mono_of_mono_left _

/-- Comparing the entire embeddings identifies arbitrary independently presented smooth factors. -/
theorem commonCoefficient_subgroup_square
    {X Y : Over (Spec (.of C))} (s : X ⟶ Y)
    (f : X ⟶ (originalSmoothBaseChangeGroup C (equation a)).X)
    (g : Y ⟶ (originalSmoothBaseChangeGroup C (equation b)).X)
    (he : (f ≫ (Over.pullback (baseMap A C)).map (smoothCurveInclusion a)) ≫
        (commonCoefficientCurveIso a b h).hom =
      (s ≫ g) ≫ (Over.pullback (baseMap B C)).map (smoothCurveInclusion b)) :
    f ≫ (commonCoefficientSmoothIso a b h).hom = s ≫ g := by
  apply (cancel_mono ((Over.pullback (baseMap B C)).map (smoothCurveInclusion b))).mp
  rw [Category.assoc, commonCoefficientIso_inclusion, ← Category.assoc]
  exact he

/-- Whole embeddings of independent character models determine the full subgroup comparison. -/
theorem commonCoefficient_character_subgroup_square (G : Type) [AddCommMonoid G]
    (f : (Over.pullback (baseMap A C)).obj (model A G) ⟶
      (originalSmoothBaseChangeGroup C (equation a)).X)
    (g : (Over.pullback (baseMap B C)).obj (model B G) ⟶
      (originalSmoothBaseChangeGroup C (equation b)).X)
    (he : (overIso A C G).hom ≫ f ≫
        (Over.pullback (baseMap A C)).map (smoothCurveInclusion a) ≫
          (commonCoefficientCurveIso a b h).hom =
      (overIso B C G).hom ≫ g ≫
        (Over.pullback (baseMap B C)).map (smoothCurveInclusion b)) :
    f ≫ (commonCoefficientSmoothIso a b h).hom =
      (commonGroupIso A B C G).hom ≫ g := by
  apply commonCoefficient_subgroup_square a b h
  apply (cancel_epi (overIso A C G).hom).mp
  simpa only [Category.assoc, commonGroupIso_recovery_assoc] using he

end FLT.Mazur.OneGonSmoothing

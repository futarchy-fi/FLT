/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CharacterCommonCoefficientRecovery
public import FLT.Mazur.OneGonCommonCoefficientSubgroup

/-!
# Recovering independent one-gon subgroup comparisons

Equality of the full embeddings over the original ring detects the subgroup
square over the common coefficient ring. The original extension need only
be injective: no flatness, reducedness, or invertibility of the order is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OneGonSmoothing
open WeierstrassIntegralChart WeierstrassDividedDepth CharacterSchemeBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A B C R G : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing R]
  [Algebra A C] [Algebra B C] [Algebra C R] [AddCommMonoid G]
  (a : A) (b : B) (h : algebraMap A C a = algebraMap B C b)
  (hinj : Function.Injective (algebraMap C R))
  (f : (Over.pullback (baseMap A C)).obj (model A G) ⟶
    (originalSmoothBaseChangeGroup C (equation a)).X)
  (g : (Over.pullback (baseMap B C)).obj (model B G) ⟶
    (originalSmoothBaseChangeGroup C (equation b)).X)

include hinj in
/-- Original whole-cubic recovery detects the actual finite-base smooth subgroup square. -/
theorem commonCoefficient_subgroup_square_of_recovery
    (he : (Over.pullback (baseMap C R)).map
        ((overIso A C G).hom ≫ f ≫
          (Over.pullback (baseMap A C)).map (smoothCurveInclusion a) ≫
            (commonCoefficientCurveIso a b h).hom) =
      (Over.pullback (baseMap C R)).map
        ((overIso B C G).hom ≫ g ≫
          (Over.pullback (baseMap B C)).map (smoothCurveInclusion b))) :
    f ≫ (commonCoefficientSmoothIso a b h).hom =
      (commonGroupIso A B C G).hom ≫ g := by
  let _ : IsSeparated (family b).hom :=
    inferInstanceAs (IsSeparated (integralCurveStructure (equation b)))
  let _ : IsSeparated ((Over.pullback (baseMap B C)).obj (family b)).hom :=
    MorphismProperty.pullback_snd _ _ inferInstance
  apply commonCoefficient_subgroup_square a b h
  have hc := commonGroupIso_square_of_recovery A B C R G hinj
    (commonCoefficientCurveIso a b h)
    (f ≫ (Over.pullback (baseMap A C)).map (smoothCurveInclusion a))
    (g ≫ (Over.pullback (baseMap B C)).map (smoothCurveInclusion b))
    (by simpa only [Category.assoc] using he)
  simpa only [Category.assoc] using hc

include hinj in
/-- Comparing on the original intrinsic character scheme suffices for full subgroup equality. -/
theorem commonCoefficient_subgroup_square_of_actual_recovery
    (he : (overIso C R G).hom ≫ (Over.pullback (baseMap C R)).map
        ((overIso A C G).hom ≫ f ≫
          (Over.pullback (baseMap A C)).map (smoothCurveInclusion a) ≫
            (commonCoefficientCurveIso a b h).hom) =
      (overIso C R G).hom ≫ (Over.pullback (baseMap C R)).map
        ((overIso B C G).hom ≫ g ≫
          (Over.pullback (baseMap B C)).map (smoothCurveInclusion b))) :
    f ≫ (commonCoefficientSmoothIso a b h).hom =
      (commonGroupIso A B C G).hom ≫ g := by
  exact commonCoefficient_subgroup_square_of_recovery a b h hinj f g
    ((cancel_epi (overIso C R G).hom).mp he)

end FLT.Mazur.OneGonSmoothing

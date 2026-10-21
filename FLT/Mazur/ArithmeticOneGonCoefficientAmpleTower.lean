/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonCoefficientAmple
public import FLT.Mazur.ArithmeticOneGonCoefficientTower
public import FLT.Mazur.CyclicBoundaryCurveTowerParameter

/-!
# Arithmetic coefficient cocycles on the actual ample charts

Successive coefficient recovery agrees with direct recovery, retaining the
original ample parameter scheme. The independently constructed coefficient
curves and their actual full-curve cocycle supply the comparison.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.ArithmeticOneGonGeneralizedCurve
open CyclicBoundaryParameter GeneralizedEllipticCurve CharacterSchemeBaseChange
open OneGonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (A B C : Type) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  (t : A) (ht : IsUnit (1 + 432 * t)) (n : ℕ) [NeZero n]

local instance coefficientTowerChart_separated {S T : Scheme}
    (E : GeneralizedEllipticCurve S) [IsSeparated E.group.hom] (g : T ⟶ S) :
    IsSeparated (E.baseChange g).group.hom :=
  inferInstanceAs (IsSeparated (pullback.snd E.group.hom g))

local instance coefficientTowerChart_smooth {S T : Scheme}
    (E : GeneralizedEllipticCurve S) [SmoothOfRelativeDimension 1 E.group.hom] (g : T ⟶ S) :
    SmoothOfRelativeDimension 1 (E.baseChange g).group.hom :=
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) E.group.hom g
    inferInstance

/-- The actual iterated full-curve coefficient comparison retains the direct ample parameter. -/
@[reassoc] theorem iteratedCoefficientAmple_original :
    ampleCurveTransport (iteratedCoefficientIso A B C t ht) n ≫
        ampleBaseChangeToOriginal (baseMap B C) ((curve t ht).baseChange (baseMap A B)) n ≫
          ampleBaseChangeToOriginal (baseMap A B) (curve t ht) n =
      coefficientAmpleToOriginal (S := C) t ht n := by
  have he : iteratedCoefficientIso A B C t ht = coefficientIso (S := C) t ht ≪≫
      (curve t ht).baseChangeCompEqIso (baseMap A B) (baseMap B C) (baseMap A C)
        (coefficientTower_baseMap A B C).symm := Iso.ext (coefficientIso_tower A B C t ht)
  rw [he, ← ampleCurveTransport_comp, Category.assoc, ampleCurveTowerParameter_original]
  rfl

/-- Independently constructed successive coefficient charts satisfy the actual scheme cocycle. -/
theorem coefficientAmpleToOriginal_tower :
    ampleCurveTransport
        (parameterIso (IsScalarTower.algebraMap_apply A B C t)
          (coefficientParameter_isUnit (S := C) t ht)
          (coefficientParameter_isUnit (S := C) _ (coefficientParameter_isUnit (S := B) t ht))) n ≫
      coefficientAmpleToOriginal (S := C) (algebraMap A B t)
        (coefficientParameter_isUnit (S := B) t ht) n ≫
      coefficientAmpleToOriginal (S := B) t ht n =
        coefficientAmpleToOriginal (S := C) t ht n := by
  rw [coefficientAmpleToOriginal, coefficientAmpleToOriginal]
  simp only [Category.assoc]
  rw [← ampleCurveTransport_baseChange_assoc]
  have he := iteratedCoefficientAmple_original A B C t ht n
  rw [iteratedCoefficientIso_def, ← ampleCurveTransport_comp,
    ← ampleCurveTransport_comp] at he
  simpa only [Category.assoc] using he

end FLT.Mazur.ArithmeticOneGonGeneralizedCurve

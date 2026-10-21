/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonParameter
public import FLT.Mazur.ArithmeticOneGonParameterIso
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# A varying generalized one-gon over an algebraic integral base

The explicit algebraic family includes the singular fiber and recovers each
permitted arithmetic parameter as a full generalized curve, with its action.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.ArithmeticOneGonParameter
open ArithmeticOneGonGeneralizedCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The finite-presentation integral parameter scheme. -/
abbrev parameterBase : Scheme := Spec (.of ParameterRing)

/-- The original structural map to the integers. -/
def toIntegers : parameterBase ⟶ Spec (.of ℤ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℤ ParameterRing))

/-- The parameter base is locally finitely presented over the integers. -/
instance toIntegers_lfp : LocallyOfFinitePresentation toIntegers := by
  apply (LocallyOfFinitePresentation.SpecMap_iff _).mpr
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

/-- The actual generalized curve on the varying algebraic base. -/
def universalCurve : GeneralizedEllipticCurve parameterBase := curve parameter factor_isUnit

/-- The universal generalized curve retains the full original projective cubic. -/
theorem universalCurve_curve : universalCurve.curve = OneGonSmoothing.family parameter := rfl

variable {R : Type} [CommRing R] (t : R) (ht : IsUnit (1 + 432 * t))

/-- The actual map classifying a permitted parameter. -/
def parameterMap : Spec (.of R) ⟶ parameterBase :=
  Spec.map (CommRingCat.ofHom (specialize t ht))

/-- The classifying map is over the original integer base. -/
@[reassoc] theorem parameterMap_over :
    parameterMap t ht ≫ toIntegers =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ R)) := by
  rw [parameterMap, toIntegers, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (Subsingleton.elim _ _)

/-- Every allowed parameter recovers the entire generalized curve, including its action. -/
irreducible_def specializationIso :
    curve t ht ≅ universalCurve.baseChange (parameterMap t ht) := by
  letI : Algebra ParameterRing R := (specialize t ht).toAlgebra
  exact parameterIso (specialize_parameter t ht).symm ht
    (coefficientParameter_isUnit parameter factor_isUnit) ≪≫
      coefficientIso parameter factor_isUnit

/-- Recovery respects the exact original structural map. -/
@[reassoc] theorem specializationIso_over :
    (specializationIso t ht).hom.curve.left ≫
      (universalCurve.baseChange (parameterMap t ht)).curve.hom =
        (curve t ht).curve.hom :=
  (specializationIso t ht).hom.curve.w

end FLT.Mazur.ArithmeticOneGonParameter

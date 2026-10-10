/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryNormalizedAction
public import Mathlib.AlgebraicGeometry.Limits

/-!
# The normalized auxiliary action is over the original arithmetic base

The normalization changes Weierstrass coefficients but preserves the map to
Spec Z[1/2]. The actual finite action is therefore an action in schemes over
that arithmetic base, with no exclusion of characteristic three.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.UniversalWeierstrass

/-- The arithmetic coefficient ring retains characteristic three. -/
abbrev AuxiliaryArithmeticRing := Localization.Away (2 : ℤ)

/-- The arithmetic base of the normalized auxiliary family. -/
def auxiliaryArithmeticBase : Scheme := Spec (.of AuxiliaryArithmeticRing)

/-- The actual inclusion of the arithmetic base in Spec Z. -/
def auxiliaryArithmeticInclusion : auxiliaryArithmeticBase ⟶ Spec (.of ℤ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℤ AuxiliaryArithmeticRing))

instance auxiliaryArithmeticInclusion_open : IsOpenImmersion auxiliaryArithmeticInclusion :=
  IsOpenImmersion.of_isLocalization (2 : ℤ)

/-- Morphisms to this arithmetic base are unique when they exist. -/
theorem auxiliaryArithmetic_hom_ext {T : Scheme} (f g : T ⟶ auxiliaryArithmeticBase) : f = g :=
  (cancel_mono auxiliaryArithmeticInclusion).mp (specZIsTerminal.hom_ext _ _)

/-- The original Weierstrass coefficient scheme is defined over Z[1/2]. -/
def auxiliaryArithmeticCoefficients : AuxiliaryArithmeticRing →+* ParameterRing :=
  IsLocalization.Away.lift (2 : ℤ)
    (show IsUnit ((Int.castRingHom ParameterRing) 2) from parameter_two_isUnit)

/-- The original level-four parameter scheme retains this arithmetic structure map. -/
def auxiliaryArithmeticStructure : levelFour.left ⟶ auxiliaryArithmeticBase :=
  levelFour.hom ≫ Spec.map (CommRingCat.ofHom auxiliaryArithmeticCoefficients)

/-- The normalized slice with its inherited arithmetic structure map. -/
def normalizedAuxiliaryArithmetic : Over auxiliaryArithmeticBase :=
  Over.mk (normalizedSliceInclusion ≫ auxiliaryArithmeticStructure)

/-- The actual normalization retraction is a morphism over the arithmetic base. -/
theorem auxiliaryNormalizationMorphism_arithmetic :
    auxiliaryNormalizationMorphism ≫ normalizedAuxiliaryArithmetic.hom =
      auxiliaryArithmeticStructure := auxiliaryArithmetic_hom_ext _ _

/-- Every relabeling on the original normalized slice preserves the arithmetic base. -/
theorem normalizedAuxiliaryAction_arithmetic (e : MulAut (Labels 4)) :
    (normalizedAuxiliaryAction e).hom ≫ normalizedAuxiliaryArithmetic.hom =
      normalizedAuxiliaryArithmetic.hom := auxiliaryArithmetic_hom_ext _ _

/-- The finite relabeling automorphism in schemes over Z[1/2]. -/
def normalizedAuxiliaryArithmeticAut (e : MulAut (Labels 4)) :
    Aut normalizedAuxiliaryArithmetic :=
  Over.isoMk (normalizedAuxiliaryAction e) (normalizedAuxiliaryAction_arithmetic e)

/-- The constructed relabelings form an action over the arithmetic base. -/
def normalizedAuxiliaryArithmeticAction :
    MulAut (Labels 4) →* Aut normalizedAuxiliaryArithmetic where
  toFun := normalizedAuxiliaryArithmeticAut
  map_one' := by
    apply Aut.ext
    apply Over.OverMorphism.ext
    exact congrArg Iso.hom (normalizedAuxiliaryAction.map_one)
  map_mul' e d := by
    apply Aut.ext
    apply Over.OverMorphism.ext
    exact congrArg Iso.hom (normalizedAuxiliaryAction.map_mul e d)

/-- The acting label group is finite, as required by the finite quotient construction. -/
instance normalizedAuxiliaryLabelGroup_finite : Finite (MulAut (Labels 4)) :=
  Finite.of_injective (fun e : MulAut (Labels 4) => (e : Labels 4 → Labels 4))
    DFunLike.coe_injective

end FLT.Mazur.UniversalWeierstrass

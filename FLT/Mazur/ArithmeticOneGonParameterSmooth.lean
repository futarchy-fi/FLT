/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonAlgebraicFamily

/-!
# The algebraic arithmetic parameter is smooth over the integers

Polynomial parameters followed by principal localization give a smooth base.
The retained zero section makes its structure map surjective in every
characteristic. These properties concern the parameter scheme, not the map
from a generalized-curve moduli problem to that scheme.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.ArithmeticOneGonParameter

/-- The integral parameter algebra is smooth, without completing the polynomial variable. -/
instance parameterRing_smooth : Algebra.Smooth ℤ ParameterRing where
  formallySmooth := inferInstance
  finitePresentation := inferInstance

/-- The algebraic parameter scheme is smooth over the entire integer base. -/
instance toIntegers_smooth : Smooth toIntegers :=
  (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    (RingHom.smooth_algebraMap.mpr inferInstance)

/-- The original degeneration parameter zero gives an integral section of the base. -/
def zeroSection : Spec (.of ℤ) ⟶ parameterBase := parameterMap 0 (by simp)

/-- The zero section lies over the identity of the integer base. -/
@[reassoc] theorem zeroSection_toIntegers : zeroSection ≫ toIntegers = 𝟙 _ := by
  rw [zeroSection, parameterMap_over]
  change Spec.map (𝟙 (CommRingCat.of ℤ)) = _
  exact Spec.map_id _

/-- Every characteristic occurs on the actual algebraic parameter scheme. -/
instance toIntegers_surjective : Surjective toIntegers := by
  constructor
  intro x
  exact ⟨zeroSection x, congrArg (fun f ↦ f x) zeroSection_toIntegers⟩

end FLT.Mazur.ArithmeticOneGonParameter

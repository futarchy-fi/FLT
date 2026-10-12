/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.LaurentPairUniversalUnits

/-!
# Sealed independent tangent and reciprocal coordinates

Keep Laurent multiplication opaque during geometric comparison. The evaluation
lemmas expose the exact original units, including their signed reciprocal scale.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.ProjectiveLineUniversalAction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (K : Type u) [Field K]

/-- The original tangent coordinate is inverse to the cyclic coordinate. -/
irreducible_def laurentPairTangentUnit : K[T;T⁻¹][T;T⁻¹]ˣ :=
  (laurentPairFirstUnit K)⁻¹

/-- The independent line coordinate keeps its prescribed signed reciprocal scale. -/
irreducible_def laurentPairReciprocalUnit (a : Kˣ) : K[T;T⁻¹][T;T⁻¹]ˣ :=
  Units.map (algebraMap K K[T;T⁻¹][T;T⁻¹]) a * (laurentPairSecondUnit K)⁻¹

variable {K} {B : Type u} [CommRing B] [Algebra K B] (q z : Bˣ)

/-- The sealed tangent coordinate evaluates to the inverse cyclic parameter. -/
theorem laurentPairEvaluation_tangentUnit :
    Units.map (laurentPairEvaluation (K := K) q z).toMonoidHom
      (laurentPairTangentUnit K) = q⁻¹ := by
  rw [laurentPairTangentUnit_def, map_inv, laurentPairEvaluation_firstUnit]

/-- The sealed reciprocal coordinate evaluates with the original signed scale. -/
theorem laurentPairEvaluation_reciprocalUnit (a : Kˣ) :
    Units.map (laurentPairEvaluation (K := K) q z).toMonoidHom
      (laurentPairReciprocalUnit K a) = Units.map (algebraMap K B) a * z⁻¹ := by
  rw [laurentPairReciprocalUnit_def, map_mul, map_inv,
    laurentPairEvaluation_constantUnit, laurentPairEvaluation_secondUnit]

end FLT.Mazur.ProjectiveLineUniversalAction

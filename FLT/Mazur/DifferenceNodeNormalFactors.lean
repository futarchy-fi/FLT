/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.DifferenceNodeCriticalTranslation
public import FLT.Mazur.NilpotentQuadraticDifferenceInverse

/-!
# Constant-product factors on the full corrected node

Translation to the constructed critical point and polynomial factorization
give a map from the actual smoothing node to the whole corrected quotient.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.DifferenceNode
variable {R : Type*} [CommRing R] (h : R[X]) (b : R)
  (I : Ideal R) (hI : IsNilpotent I) (hh : h ∈ I.map C)

/-- The translated quadratic correction, with every coefficient retained. -/
def normalCorrection : R[X] :=
  NilpotentPolynomialInverse.quadraticRemainder h (criticalDifference h b I hI hh)

/-- The remaining quadratic correction is nilpotent coefficient by coefficient. -/
theorem normalCorrection_mem : normalCorrection h b I hI hh ∈ I.map C :=
  NilpotentPolynomialInverse.quadraticRemainder_mem I h hh _

local notation "K" => normalCorrection h b I hI hh
local notation "hK" => normalCorrection_mem h b I hI hh
local notation "a" => criticalSlope h b I hI hh
local notation "c" => smoothingConstant h b I hI hh
local notation "A" => Coordinate h b
local notation "f" => algebraMap R A
local notation "u" => p h b - f a
local notation "v" => q h b + f a

/-- The first constant-product factor on the full corrected node. -/
def normalSmall : A := NilpotentQuadraticDifference.smallFactor K I hI hK f u v

/-- The second constant-product factor on the full corrected node. -/
def normalOpposite : A := NilpotentQuadraticDifference.oppositeFactor K I hI hK f u v

/-- The factors have the actual constructed smoothing constant as product. -/
theorem normalFactors_product : normalSmall h b I hI hh * normalOpposite h b I hI hh = f c := by
  have he := criticalTranslation_relation h b I hI hh f (p h b) (q h b) (relation h b)
  have hf := NilpotentQuadraticDifference.factors_product K I hI hK f u v
  change normalSmall h b I hI hh * normalOpposite h b I hI hh =
    u * v - (v - u) ^ 2 * Polynomial.eval₂ f (v - u) K at hf
  change u * v = f c + (v - u) ^ 2 * Polynomial.eval₂ f (v - u) K at he
  linear_combination hf + he

/-- The complete constant-product node maps into the original corrected coordinate algebra. -/
def normalBackward : NodalFiber.Coordinate c →ₐ[R] A :=
  NodalFiber.evaluation c (normalSmall h b I hI hh) (normalOpposite h b I hI hh)
    (normalFactors_product h b I hI hh)

/-- The first smoothing-node coordinate is the constructed first factor. -/
@[simp] theorem normalBackward_p :
    normalBackward h b I hI hh (NodalFiber.p c) = normalSmall h b I hI hh :=
  NodalFiber.evaluation_p ..

/-- The second smoothing-node coordinate is the constructed opposite factor. -/
@[simp] theorem normalBackward_q :
    normalBackward h b I hI hh (NodalFiber.q c) = normalOpposite h b I hI hh :=
  NodalFiber.evaluation_q ..

end FLT.Mazur.DifferenceNode

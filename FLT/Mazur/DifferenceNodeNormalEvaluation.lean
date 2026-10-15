/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.DifferenceNodeNormalFactors

/-!
# Evaluating the full corrected node on the constant-product node

The inverse factor difference and the inverse critical translation recover
both original tangent coordinates, including at the node.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.DifferenceNode
variable {R : Type*} [CommRing R] (h : R[X]) (b : R)
  (I : Ideal R) (hI : IsNilpotent I) (hh : h ∈ I.map C)
  {S : Type*} [CommRing S] [Algebra R S] (u v : S)
local notation "K" => normalCorrection h b I hI hh
local notation "hK" => normalCorrection_mem h b I hI hh
local notation "a" => criticalSlope h b I hI hh
local notation "c" => smoothingConstant h b I hI hh
local notation "f" => algebraMap R S
local notation "D" => NilpotentQuadraticDifference.inverseDifference K I hI hK f u v
local notation "r" => NilpotentQuadraticDifference.factorRoot K I hI hK
local notation "E" => Polynomial.eval₂ (algebraMap R S)
  (NilpotentQuadraticDifference.inverseDifference K I hI hK (algebraMap R S) u v)
  (NilpotentQuadraticDifference.factorRoot K I hI hK)

variable (huv : u * v = algebraMap R S (smoothingConstant h b I hI hh))

include huv in
/-- The recovered pair satisfies the original corrected quotient equation. -/
theorem normalEvaluation_equation :
    (u - D * E + f a) * (v + D * E - f a) =
      h.eval₂ f ((v + D * E - f a) - (u - D * E + f a) - f b) := by
  have he := criticalTranslation_identity h b I hI hh f
    (u - D * E + f a) (v + D * E - f a)
  simp only [add_sub_cancel_right, sub_add_cancel] at he
  have hf := NilpotentQuadraticDifference.factors_product K I hI hK f
    (u - D * E) (v + D * E)
  rw [NilpotentQuadraticDifference.inverseDifference_small,
    NilpotentQuadraticDifference.inverseDifference_opposite] at hf
  change (u - D * E + f a) * (v + D * E - f a) -
    h.eval₂ f ((v + D * E - f a) - (u - D * E + f a) - f b) =
      (u - D * E) * (v + D * E) - f c -
        (v + D * E - (u - D * E)) ^ 2 *
          Polynomial.eval₂ f (v + D * E - (u - D * E)) K at he
  linear_combination he - hf + huv

/-- The recovered pair defines an actual map from the full corrected quotient. -/
def normalEvaluation : Coordinate h b →ₐ[R] S :=
  evaluation h b (u - D * E + f a) (v + D * E - f a)
    (normalEvaluation_equation h b I hI hh u v huv)

/-- The recovered first original tangent includes its critical translation. -/
@[simp] theorem normalEvaluation_p :
    normalEvaluation h b I hI hh u v huv (p h b) = u - D * E + f a := evaluation_p ..

/-- The recovered second original tangent includes the opposite critical translation. -/
@[simp] theorem normalEvaluation_q :
    normalEvaluation h b I hI hh u v huv (q h b) = v + D * E - f a := evaluation_q ..

/-- The recovered pair maps to the first prescribed constant-product factor. -/
theorem normalEvaluation_small :
    normalEvaluation h b I hI hh u v huv (normalSmall h b I hI hh) = u := by
  rw [normalSmall, NilpotentQuadraticDifference.smallFactor_map]
  simp only [map_sub, map_add, AlgHom.commutes, normalEvaluation_p, normalEvaluation_q,
    add_sub_cancel_right, sub_add_cancel]
  exact NilpotentQuadraticDifference.inverseDifference_small K I hI hK f u v

/-- The recovered pair maps to the second prescribed constant-product factor. -/
theorem normalEvaluation_opposite :
    normalEvaluation h b I hI hh u v huv (normalOpposite h b I hI hh) = v := by
  rw [normalOpposite, NilpotentQuadraticDifference.oppositeFactor_map]
  simp only [map_sub, map_add, AlgHom.commutes, normalEvaluation_p, normalEvaluation_q,
    add_sub_cancel_right, sub_add_cancel]
  exact NilpotentQuadraticDifference.inverseDifference_opposite K I hI hK f u v

end FLT.Mazur.DifferenceNode

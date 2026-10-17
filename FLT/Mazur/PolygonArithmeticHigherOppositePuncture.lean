/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticHigherNodeIdentification

/-!
# The opposite puncture of an annihilated higher correction

The whole-node identification fixes the opposite coordinate. The original
puncture square therefore fixes the complete opposite Laurent substitution.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticStages
open LaurentPolynomial PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable (R : Type*) [CommRing R] (π : R) (m r : ℕ)

/-- An annihilated higher correction fixes the entire opposite puncture. -/
theorem correctionPunctureFactor_higher_opposite (t : Quotient R π m)
    (ht : parameter R π m ^ (r + 1) * t = 0) (q : R[T;T⁻¹]) :
    correctionPunctureFactor R π m t (higherCorrectionField R π r q) false =
      AlgEquiv.refl := by
  let v := higherCorrectionField R π r q
  let s := correctionSmoothing R π m t v
  have hy : (correctionNodeFactor R π m t v).toAlgHom (rightCoordinate s) =
      rightCoordinate t := by
    have h := DFunLike.congr_fun (correctionNodeFactor_higher_eq R π m r t ht q)
      (rightCoordinate s)
    change (correctionNodeFactor R π m t v).toAlgHom (rightCoordinate s) =
      squareZeroShear t (parameter R π m ^ (r + 1)) ht _
        (ringMap (RingHom.id _) s t (correctionSmoothing_higher_eq R π m r t ht q)
          (rightCoordinate s)) at h
    rw [ringMap_right, squareZeroShear_right] at h
    exact h
  apply AlgEquiv.coe_toAlgHom_injective
  apply LaurentNilpotentReparametrization.hom_ext_positive
  have h := AlgHom.congr_fun (correctionNodeFactor_puncture R π m t v false)
    (rightCoordinate s)
  simp only [AlgHom.comp_apply, hy, s, punctureLaurentMap, branchSwapMap_right,
    leftLaurentMap_left] at h
  exact h.symm

end FLT.Mazur.PolygonArithmeticStages

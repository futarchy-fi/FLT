/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundedPolynomialBaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Coherence of bounded polynomial coefficient extension

Successive extensions of the original bounded polynomial ambient agree with
extension along the composite coefficient map, including every coefficient.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.HilbertChart
universe u
variable (R S T I : Type u) [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T] (n : ℕ)

/-- Extending bounded polynomials in two stages equals direct coefficient extension. -/
theorem boundedPolynomialBaseChangeEquiv_tower :
    ((boundedPolynomialBaseChangeEquiv R S I n).baseChange S T).trans
        (boundedPolynomialBaseChangeEquiv S T I n) =
      (AlgebraTensorModule.cancelBaseChange R S T T
        (MvPolynomial.restrictTotalDegree I R n)).trans
          (boundedPolynomialBaseChangeEquiv R T I n) := by
  apply LinearEquiv.toLinearMap_injective
  apply (((boundedPolynomialBasis R I n).baseChange S).baseChange T).ext
  intro m
  simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, Module.Basis.baseChange_apply,
    LinearEquiv.baseChange_tmul, boundedPolynomialBaseChangeEquiv_basis,
    AlgebraTensorModule.cancelBaseChange_tmul, one_smul]

end FLT.Mazur.HilbertChart

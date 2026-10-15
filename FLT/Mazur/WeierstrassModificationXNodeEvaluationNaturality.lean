/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXNodeInverseFunctions

/-!
# Full initial node evaluation commutes with algebra maps

Uniqueness of the corrected inverse incidence identifies the independently
constructed target parameter without expanding its nilpotent iteration.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A] (g : S →ₐ[R] A)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R) (r : R[X])
  (hr : r ^ 2 + polynomialSlopeLinear W b3 * r = polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
  (p q : S) (hu : IsUnit (q + algebraMap R S W.a₁))
  (hpq : p * q = algebraMap R S s)
  (hu' : IsUnit (g q + algebraMap R A W.a₁))
  (hpq' : g p * g q = algebraMap R A s)

/-- The full corrected inverse incidence is natural in the target algebra. -/
theorem polynomialNodeInverseT_algHom :
    g (polynomialNodeInverseT b3 r I hI hrI h3 W p q hu) =
      polynomialNodeInverseT b3 r I hI hrI h3 W (g p) (g q) hu' := by
  apply polynomialNodeParameter_unique b3 r I hI hrI h3 W (g p) (g q) hu'
  · have h := congrArg g (polynomialNodeInverseT_equation b3 r I hI hrI h3 W p q hu)
    simpa only [map_mul, map_add, AlgHom.commutes, Polynomial.algHom_eval₂_algebraMap]
      using h
  · exact polynomialNodeInverseT_equation b3 r I hI hrI h3 W (g p) (g q) hu'

/-- Every original initial function commutes with the constructed full node evaluation. -/
theorem polynomialNodeEvaluation_algHom :
    g.comp (polynomialNodeEvaluation W s b3 b4 b6 r hr I hI hrI h3 p q hu hpq) =
      polynomialNodeEvaluation W s b3 b4 b6 r hr I hI hrI h3 (g p) (g q) hu' hpq' := by
  apply hom_ext
  · simp only [AlgHom.comp_apply, polynomialNodeEvaluation_t]
    exact polynomialNodeInverseT_algHom g W b3 r I hI hrI h3 p q hu hu'
  · simp only [AlgHom.comp_apply, polynomialNodeEvaluation_v, map_add,
      Polynomial.algHom_eval₂_algebraMap]
    rw [polynomialNodeInverseT_algHom g W b3 r I hI hrI h3 p q hu hu']

end FLT.Mazur.WeierstrassModificationX

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXNodeFactorCoefficient
public import FLT.Mazur.WeierstrassModificationXPolynomialFactorRatioEquiv
public import FLT.Mazur.NodalFiberTangentCoefficientMap
public import FLT.Mazur.WeierstrassModificationXInitialMobiusNormalization

/-!
# Coefficient compatibility of the full corrected arithmetic node equivalence

The original coefficient map commutes with the full factor-ratio isomorphism
and its constructed inverse, with separately named target smoothing.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (ha : IsUnit W.a₁) (s τ : R)
  (hτ : s = W.a₁ ^ 2 * τ) (τ' : S) (hτ' : f s = (W.map f).a₁ ^ 2 * τ') (ht : f τ = τ')
  (b3 b4 b6 : R) (r : R[X])
  (hr : r ^ 2 + polynomialSlopeLinear W b3 * r = polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (J : Ideal S) (hf : I ≤ J.comap f)
  (hI : IsNilpotent I) (hJ : IsNilpotent J) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "U" => W.map f
local notation "hrJ" => polynomialArithmeticIdeal_coefficient f I J hf hrI
local notation "hr'" => polynomialRootEquation_coefficient f W b3 b4 b6 r hr
local notation "F" => polynomialFactorRatioMap W ha s τ hτ b3 b4 b6 r hr I hI hrI h3
local notation "F'" => polynomialFactorRatioMap U (ha.map f) (f s) τ' hτ'
  (f b3) (f b4) (f b6) (r.map f) hr' J hJ hrJ (hf h3)
local notation "E" => polynomialFactorRatioEquiv W ha s τ hτ b3 b4 b6 r hr I hI hrI h3
local notation "E'" => polynomialFactorRatioEquiv U (ha.map f) (f s) τ' hτ'
  (f b3) (f b4) (f b6) (r.map f) hr' J hJ hrJ (hf h3)
local notation "g" => nodeOpenCoefficientRingMap f W s
local notation "d" => NodalFiber.tangentCoefficientRingMap f τ (-1 : R) τ' (-1 : S) ht (by simp)
local notation "G'" => polynomialNodeForwardBase U (f s) (f b3) (f b4) (f b6)
  (r.map f) hr' J hJ hrJ (hf h3)

/-- The full corrected map commutes on every function with the original coefficient map. -/
theorem polynomialFactorRatioMap_coefficient : (g).comp (F).toRingHom =
    (F').toRingHom.comp d := by
  apply NodalFiber.tangent_ringHom_ext
  · intro x
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgHom.commutes, nodeOpenCoefficientRingMap_scalar,
      NodalFiber.tangentCoefficientRingMap_scalar]
  · change g (F (NodalFiber.tangentP τ (-1 : R))) =
      F' (d (NodalFiber.tangentP τ (-1 : R)))
    rw [NodalFiber.tangentCoefficientRingMap_p,
      polynomialFactorRatioMap_p_node, polynomialFactorRatioMap_p_node]
    rw [map_mul, map_mul, map_pow, nodeOpenCoefficientRingMap_scalar]
    have hi := congrArg (fun z : Sˣ ↦ (↑z⁻¹ : S)) (initialTangentUnit_map W ha f)
    change f (↑(zeroInitialTangentUnit W ha)⁻¹ : R) =
      (↑(zeroInitialTangentUnit U (ha.map f))⁻¹ : S) at hi
    rw [hi]
    change _ * g (algebraMap _ _ (NodalFiber.p s)) * _ = _
    rw [nodeOpenCoefficientRingMap_p,
      polynomialNodeForwardBase_opposite_coefficient f W s b3 b4 b6 r hr I J hf hI hJ hrI h3]
    rfl
  · change g (F (NodalFiber.tangentQ τ (-1 : R))) =
      F' (d (NodalFiber.tangentQ τ (-1 : R)))
    rw [NodalFiber.tangentCoefficientRingMap_q]
    apply (polynomialNodeForwardBase_opposite_isUnit U (f s) (f b3) (f b4) (f b6)
      (r.map f) hr' J hJ hrJ (hf h3)).mul_right_cancel
    rw [polynomialFactorRatioMap_q_denominator]
    have hd := congrArg g
      (polynomialFactorRatioMap_q_denominator W ha s τ hτ b3 b4 b6 r hr I hI hrI h3)
    rw [map_mul,
      polynomialNodeForwardBase_opposite_coefficient f W s b3 b4 b6 r hr I J hf hI hJ hrI h3,
      polynomialNodeForwardBase_small_coefficient f W s b3 b4 b6 r hr I J hf hI hJ hrI h3] at hd
    exact hd

/-- The constructed inverse follows the same original coefficient restriction on every function. -/
theorem polynomialFactorRatioEquiv_symm_coefficient (x : PolynomialNodeOpen W s) :
    d ((E).symm x) = (E').symm (g x) := by
  apply (E').injective
  rw [AlgEquiv.apply_symm_apply]
  have h := congrArg (fun k ↦ k ((E).symm x))
    (polynomialFactorRatioMap_coefficient f W ha s τ hτ τ' hτ' ht
      b3 b4 b6 r hr I J hf hI hJ hrI h3)
  change g (E ((E).symm x)) = E' (d ((E).symm x)) at h
  rw [AlgEquiv.apply_symm_apply] at h
  exact h.symm

end FLT.Mazur.WeierstrassModificationX

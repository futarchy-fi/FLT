/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXNodeInverseCoefficientNaturality
public import FLT.Mazur.WeierstrassModificationXCoefficientRingMap
public import FLT.Mazur.WeierstrassModificationXPolynomialNodeGeometry

/-!
# Every function on the full initial node commutes with coefficient change

The inverse incidence and complete polynomial slope correction identify the
full original evaluation square, hence the actual scheme chart square.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R) (r : R[X])
  (hr : r ^ 2 + polynomialSlopeLinear W b3 * r = polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (J : Ideal S) (hf : I ≤ J.comap f)
  (hI : IsNilpotent I) (hJ : IsNilpotent J) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "U" => W.map f
local notation "hrJ" => polynomialArithmeticIdeal_coefficient f I J hf hrI

include hr in
/-- The transported full polynomial root satisfies the target conic equation. -/
theorem polynomialRootEquation_coefficient :
    r.map f ^ 2 + polynomialSlopeLinear U (f b3) * r.map f =
      polynomialSlopeConstant U (f b4) (f b6) := by
  simpa only [map_pow, map_add, map_mul, polynomialSlopeLinear_coefficient,
    polynomialSlopeConstant_coefficient, Polynomial.coe_mapRingHom] using
    congrArg (Polynomial.mapRingHom f) hr

local notation "hr'" => polynomialRootEquation_coefficient f W b3 b4 b6 r hr
local notation "F₀" => polynomialNodeForwardBase W s b3 b4 b6 r hr I hI hrI h3
local notation "F₁" => polynomialNodeForwardBase U (f s) (f b3) (f b4) (f b6)
  (r.map f) hr' J hJ hrJ (hf h3)
local notation "g" => nodeOpenCoefficientRingMap f W s
local notation "c" => coefficientRingMap f W s b3 b4 b6

/-- The original full initial evaluation commutes on every ring element. -/
theorem polynomialNodeForwardBase_coefficient :
    (g).comp (F₀).toRingHom = (F₁).toRingHom.comp c := by
  apply coefficient_ringHom_ext W s b3 b4 b6
  · intro a
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgHom.commutes, coefficientRingMap_scalar, nodeOpenCoefficientRingMap_scalar]
  · change g (F₀ (t W s b3 b4 b6)) = F₁ (c (t W s b3 b4 b6))
    rw [coefficientRingMap_t]
    dsimp only [polynomialNodeForwardBase]
    rw [polynomialNodeEvaluation_t, polynomialNodeEvaluation_t]
    exact polynomialNodeInverseT_coefficient f W s b3 r I J hf hI hJ hrI h3
  · change g (F₀ (v W s b3 b4 b6)) = F₁ (c (v W s b3 b4 b6))
    rw [coefficientRingMap_v]
    dsimp only [polynomialNodeForwardBase]
    rw [polynomialNodeEvaluation_v, polynomialNodeEvaluation_v, map_add,
      nodeOpenCoefficientRingMap_q, nodeOpenCoefficientRingMap_eval,
      polynomialNodeInverseT_coefficient]

/-- The full initial chart, including incidence zero, has its actual coefficient square. -/
@[reassoc] theorem polynomialNodeChart_coefficient :
    Spec.map (CommRingCat.ofHom g) ≫ polynomialNodeChart W s b3 b4 b6 r hr I hI hrI h3 =
      polynomialNodeChart U (f s) (f b3) (f b4) (f b6) (r.map f) hr' J hJ hrJ (hf h3) ≫
        Spec.map (CommRingCat.ofHom c) := by
  rw [polynomialNodeChart_eq_spec, polynomialNodeChart_eq_spec]
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun h ↦ Spec.map (CommRingCat.ofHom h))
    (polynomialNodeForwardBase_coefficient f W s b3 b4 b6 r hr I J hf hI hJ hrI h3)

end FLT.Mazur.WeierstrassModificationX

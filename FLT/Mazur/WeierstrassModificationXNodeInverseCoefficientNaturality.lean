/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXNodeOpenCoefficientMap
public import FLT.Mazur.WeierstrassModificationXPolynomialCoefficientNaturality

/-!
# The full inverse incidence parameter commutes with coefficient change

Uniqueness in the target nilpotent ideal identifies the complete inverse
parameter. The argument preserves the actual initial neighborhood D(q+a₁).
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (s : R)
local notation "U" => W.map f
local notation "L" => PolynomialNodeOpen W s
local notation "L'" => PolynomialNodeOpen U (f s)
local notation "g" => nodeOpenCoefficientRingMap f W s
local notation "P" => algebraMap (NodalFiber.Coordinate s) L (NodalFiber.p s)
local notation "Q" => algebraMap (NodalFiber.Coordinate s) L (NodalFiber.q s)
local notation "P'" => algebraMap (NodalFiber.Coordinate (f s)) L' (NodalFiber.p (f s))
local notation "Q'" => algebraMap (NodalFiber.Coordinate (f s)) L' (NodalFiber.q (f s))

/-- Polynomial evaluation retains the full coefficient map on the original node open. -/
theorem nodeOpenCoefficientRingMap_eval (r : R[X]) (z : L) :
    g (r.eval₂ (algebraMap R L) z) =
      (r.map f).eval₂ (algebraMap S L') (g z) := by
  rw [Polynomial.hom_eval₂, Polynomial.eval₂_map]
  congr 1
  exact RingHom.ext (nodeOpenCoefficientRingMap_scalar f W s)

variable (b3 : R) (r : R[X]) (I : Ideal R) (J : Ideal S)
  (hf : I ≤ J.comap f) (hI : IsNilpotent I) (hJ : IsNilpotent J)
  (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "hrJ" => polynomialArithmeticIdeal_coefficient f I J hf hrI
local notation "T" => polynomialNodeInverseT b3 r I hI hrI h3 W P Q
  (polynomialNodeOpen_unit W s)
local notation "T'" => polynomialNodeInverseT (f b3) (r.map f) J hJ hrJ (hf h3) U P' Q'
  (polynomialNodeOpen_unit U (f s))

/-- The independently constructed inverse incidence parameter retains every correction. -/
theorem polynomialNodeInverseT_coefficient : g T = T' := by
  apply polynomialNodeParameter_unique (f b3) (r.map f) J hJ hrJ (hf h3) U P' Q'
    (polynomialNodeOpen_unit U (f s))
  · have h := congrArg g
      (polynomialNodeInverseT_equation b3 r I hI hrI h3 W P Q
        (polynomialNodeOpen_unit W s))
    simpa only [map_mul, map_add, nodeOpenCoefficientRingMap_scalar,
      nodeOpenCoefficientRingMap_p, nodeOpenCoefficientRingMap_q,
      nodeOpenCoefficientRingMap_eval, WeierstrassCurve.map_a₁] using h
  · exact polynomialNodeInverseT_equation (f b3) (r.map f) J hJ hrJ (hf h3) U P' Q'
      (polynomialNodeOpen_unit U (f s))

end FLT.Mazur.WeierstrassModificationX

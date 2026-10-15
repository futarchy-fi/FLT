/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationTerminalCoordinateNaturality
public import FLT.Mazur.WeierstrassDilatationSmoothingNaturality
public import FLT.Mazur.NodalFiberCoefficientMap

/-!
# The full terminal normalization commutes with coefficient extension

Both directions of the constructed node equivalence commute with the actual
cubic and node coefficient maps. No compatibility of normalization is assumed.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassDilatation
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R) (r : R[X])
  (I : Ideal R) (hI : IsNilpotent I) (J : Ideal S) (hJ : IsNilpotent J)
  (hf : I ≤ J.comap (algebraMap R S)) (hrI : r ∈ I.map C) (ha : IsUnit W.a₁)
  (h4 : b4 ∈ I) (h6 : b6 ∈ I)
  (hr : r ^ 2 + C W.a₁ * r = C W.a₂ + C s * X)
local notation "f" => algebraMap R S
local notation "U" => W.map f
local notation "g" => coefficientMap W s b3 b4 b6 S
local notation "hrJ" => terminalPolynomialIdeal_map f I J hf hrI

include hr in
/-- The full tangent equation is preserved by the original coefficient homomorphism. -/
theorem terminalTangentEquation_map :
    (r.map f) ^ 2 + C (U).a₁ * r.map f = C (U).a₂ + C (f s) * X := by
  simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_C, Polynomial.map_X, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂]
    using congrArg (Polynomial.map f) hr

local notation "hr'" => terminalTangentEquation_map W s r hr (S := S)
local notation "c" => terminalSmoothing W b3 b4 b6 r I hI hrI ha h4 h6
local notation "d" => terminalSmoothing U (f b3) (f b4) (f b6) (r.map f)
  J hJ hrJ (ha.map f) (hf h4) (hf h6)
local notation "hc" => terminalSmoothing_map f W b3 b4 b6 r I hI J hJ hf hrI ha h4 h6
local notation "N" => NodalFiber.coefficientMap c d hc
local notation "e" => terminalNodeEquiv W s b3 b4 b6 r I hI hrI ha h4 h6 hr
local notation "e'" => terminalNodeEquiv U (f s) (f b3) (f b4) (f b6) (r.map f)
  J hJ hrJ (ha.map f) (hf h4) (hf h6) hr'

/-- The inverse normalization square commutes on the whole node algebra. -/
theorem terminalNodeEquiv_symm_coefficients :
    (g).comp (e).symm.toAlgHom = ((e').symm.toAlgHom.restrictScalars R).comp N := by
  apply NodalFiber.hom_ext
  · change g ((e).symm (NodalFiber.p c)) = (e').symm (N (NodalFiber.p c))
    rw [NodalFiber.coefficientMap_p, terminalNodeEquiv_symm_p]
    exact (terminalNodeSmall_coefficients W s b3 b4 b6 r I hI J hJ hf hrI ha h4 h6).trans
      (terminalNodeEquiv_symm_p U (f s) (f b3) (f b4) (f b6) (r.map f)
        J hJ hrJ (ha.map f) (hf h4) (hf h6) hr').symm
  · change g ((e).symm (NodalFiber.q c)) = (e').symm (N (NodalFiber.q c))
    rw [NodalFiber.coefficientMap_q, terminalNodeEquiv_symm_q]
    exact (terminalNodeOpposite_coefficients W s b3 b4 b6 r I hI J hJ hf hrI ha h4 h6).trans
      (terminalNodeEquiv_symm_q U (f s) (f b3) (f b4) (f b6) (r.map f)
        J hJ hrJ (ha.map f) (hf h4) (hf h6) hr').symm

/-- The forward normalization square also commutes on every original cubic function. -/
theorem terminalNodeEquiv_coefficients :
    ((e').toAlgHom.restrictScalars R).comp g = (N).comp (e).toAlgHom := by
  apply AlgHom.ext
  intro z
  have h := DFunLike.congr_fun
    (terminalNodeEquiv_symm_coefficients W s b3 b4 b6 r I hI J hJ hf hrI ha h4 h6 hr) (e z)
  change g ((e).symm (e z)) = (e').symm (N (e z)) at h
  simpa only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply, AlgEquiv.apply_symm_apply] using congrArg e' h

end FLT.Mazur.WeierstrassDilatation

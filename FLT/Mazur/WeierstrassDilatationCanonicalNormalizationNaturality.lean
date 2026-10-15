/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationTerminalNormalizationNaturality
public import FLT.Mazur.WeierstrassDilatationCoefficientRingMap
public import FLT.Mazur.NodalFiberCoefficientRingMap

/-!
# Coefficient restriction of the constructed canonical terminal normalization

The tangent roots and smoothing constants are constructed independently over
both coefficient rings. Their naturality proves the full normalization square.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassDilatation
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] terminalTangentRoot terminalSmoothing terminalNodeEquiv
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (I : Ideal R) (hI : IsNilpotent I) (J : Ideal S) (hJ : IsNilpotent J)
  (hf : I ≤ J.comap f) (ha : IsUnit W.a₁)
  (hs : s ∈ I) (h2 : W.a₂ ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "r" => terminalTangentRoot W s I hI ha hs h2
local notation "r'" => terminalTangentRoot (W.map f) (f s) J hJ (ha.map f) (hf hs) (hf h2)
local notation "hrI" => terminalTangentRoot_mem W s I hI ha hs h2
local notation "hrJ" => terminalTangentRoot_mem (W.map f) (f s) J hJ
  (ha.map f) (hf hs) (hf h2)
local notation "c" => terminalSmoothing W b3 b4 b6 r I hI hrI ha h4 h6
local notation "d" => terminalSmoothing (W.map f) (f b3) (f b4) (f b6) r'
  J hJ hrJ (ha.map f) (hf h4) (hf h6)
local notation "e" => canonicalTerminalNodeEquiv W s b3 b4 b6 I hI ha h4 h6 hs h2
local notation "e'" => canonicalTerminalNodeEquiv (W.map f) (f s) (f b3) (f b4) (f b6)
  J hJ (ha.map f) (hf h4) (hf h6) (hf hs) (hf h2)

/-- The independently constructed smoothing constants follow the original coefficient map. -/
theorem canonicalTerminalSmoothing_map : f c = d := by
  have h := terminalSmoothing_map f W b3 b4 b6 r I hI J hJ hf hrI ha h4 h6
  simpa only [terminalTangentRoot_map f I J hf W s hI hJ ha hs h2] using h

local notation "hc" => canonicalTerminalSmoothing_map f W s b3 b4 b6 I hI J hJ
  hf ha hs h2 h4 h6
local notation "N" => NodalFiber.coefficientRingMap f c d hc
local notation "g" => coefficientRingMap f W s b3 b4 b6

/-- The canonical inverse normalization commutes on the entire original node algebra. -/
theorem canonicalTerminalNodeEquiv_symm_map :
    (g).comp (e).symm.toAlgHom.toRingHom = (e').symm.toAlgHom.toRingHom.comp N := by
  let _ := f.toAlgebra
  apply NodalFiber.coefficient_ringHom_ext c
  · intro a
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgHom.commutes, coefficientRingMap_algebraMap, NodalFiber.coefficientRingMap_algebraMap]
  · change g ((e).symm (NodalFiber.p c)) = (e').symm (N (NodalFiber.p c))
    rw [NodalFiber.coefficientRingMap_p]
    change g ((terminalNodeEquiv W s b3 b4 b6 r I hI hrI ha h4 h6
      (terminalTangentRoot_equation W s I hI ha hs h2)).symm (NodalFiber.p c)) = _
    rw [terminalNodeEquiv_symm_p]
    have h := terminalNodeSmall_coefficients W s b3 b4 b6 r I hI J hJ hf hrI ha h4 h6
    simp only [RingHom.algebraMap_toAlgebra,
      terminalTangentRoot_map f I J hf W s hI hJ ha hs h2] at h
    exact h.trans (terminalNodeEquiv_symm_p (W.map f) (f s) (f b3) (f b4) (f b6)
      r' J hJ hrJ (ha.map f) (hf h4) (hf h6)
      (terminalTangentRoot_equation (W.map f) (f s) J hJ (ha.map f) (hf hs) (hf h2))).symm
  · change g ((e).symm (NodalFiber.q c)) = (e').symm (N (NodalFiber.q c))
    rw [NodalFiber.coefficientRingMap_q]
    change g ((terminalNodeEquiv W s b3 b4 b6 r I hI hrI ha h4 h6
      (terminalTangentRoot_equation W s I hI ha hs h2)).symm (NodalFiber.q c)) = _
    rw [terminalNodeEquiv_symm_q]
    have h := terminalNodeOpposite_coefficients W s b3 b4 b6 r I hI J hJ hf hrI ha h4 h6
    simp only [RingHom.algebraMap_toAlgebra,
      terminalTangentRoot_map f I J hf W s hI hJ ha hs h2] at h
    exact h.trans (terminalNodeEquiv_symm_q (W.map f) (f s) (f b3) (f b4) (f b6)
      r' J hJ hrJ (ha.map f) (hf h4) (hf h6)
      (terminalTangentRoot_equation (W.map f) (f s) J hJ (ha.map f) (hf hs) (hf h2))).symm

/-- The canonical forward normalization commutes on every original cubic function. -/
theorem canonicalTerminalNodeEquiv_map :
    (e').toAlgHom.toRingHom.comp g = (N).comp (e).toAlgHom.toRingHom := by
  apply RingHom.ext
  intro z
  have h := DFunLike.congr_fun
    (canonicalTerminalNodeEquiv_symm_map f W s b3 b4 b6 I hI J hJ hf ha hs h2 h4 h6) (e z)
  change g ((e).symm (e z)) = (e').symm (N (e z)) at h
  simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply, AlgEquiv.apply_symm_apply] using congrArg e' h

end FLT.Mazur.WeierstrassDilatation

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalReflectedSource

/-!
# The original secant algebra on the normalized source

The shear fixes abscissae, so the actual normalized localization still receives
all of the original secant algebra. Its original slope is the sheared slope
plus the finite shear parameter.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] rootShearCurve nodalSecondShear nodalSecondQuotient
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [IsDomain R] [IsLocalRing R] [Module.Flat R S]
  {W : WeierstrassCurve R} {π : R} {k l m : ℕ}
  (D : SplitNodeDepth W π m) (d : Data W π k) (e : Data W π l)
  (hkl : k ≤ l) (hl : 2 * l ≤ m) (hm : m ≤ k + 2 * l)
  (z : Data W π (m - k - l))
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
local notation "σ" => nodalSecondShear D (m - 2 * l)
local notation "V" => rootShearCurve W σ
local notation "sd" => (⟨d.b3, d.b4 - σ * d.b3, d.b6,
  (shearData d σ).factor3, (shearData d σ).factor4,
  (shearData d σ).factor6⟩ : Data V π k)
local notation "se" => (⟨e.b3, e.b4 - σ * e.b3, e.b6,
  (shearData e σ).factor3, (shearData e σ).factor4,
  (shearData e σ).factor6⟩ : Data V π l)
local notation "sz" => (⟨z.b3, z.b4 - σ * z.b3, z.b6,
  (shearData z σ).factor3, (shearData z σ).factor4,
  (shearData z σ).factor6⟩ : Data V π (m - k - l))
local notation "N" => nodalSecondShear_depth D (m - 2 * l)
local notation "b2" => nodalSecondQuotient D (m - 2 * l)
local notation "h2" => nodalSecondQuotient_factor D (m - 2 * l)
local notation "a'" => branchShearInput W (π ^ k) d.b3 d.b4 d.b6 σ a
local notation "c'" => branchShearInput W (π ^ l) e.b3 e.b4 e.b6 σ c
local notation "B" => SumDepthSourceRing sd se a' c'
local notation "j" => IsScalarTower.toAlgHom R S B
local notation "aa" => (j).comp a'
local notation "cc" => (j).comp c'
local notation "hc" => sumDepthSource_leftUnit sd se a' c'
local notation "hd" => sumDepthSource_rightUnit sd se a' c'
local notation "hxu" => sumDepthSource_abscissaUnit sd se a' c'
local notation "i" => sumDepthSourceInverse sd se a' c' D.uniformizer_ne_zero hkl
local notation "L" => sumDepthSourceSlope sd se a' c' D.uniformizer_ne_zero hkl
local notation "hi" => sumDepthSourceInverse_relation sd se a' c' D.uniformizer_ne_zero hkl
local notation "hL" => sumDepthSourceSlope_relation sd se a' c' D.uniformizer_ne_zero hkl
local notation "c₀" => unequalDepthRight D.uniformizer_ne_zero d e hkl c
local notation "dx" => a (x W (π ^ k) d.b3 d.b4 d.b6) -
  c₀ (x W (π ^ k) d.b3 d.b4 d.b6)
local notation "T" => UnequalDepthSecantRing D.uniformizer_ne_zero d e hkl a c

omit [Module.Flat R S] in
/-- The original secant denominator is a unit on the normalized localization. -/
theorem nodalReflectedSecant_unit : IsUnit ((j) dx) := by
  simpa only [unequalDepthRight_x, branchShearInput_x, IsScalarTower.coe_toAlgHom'] using
    (sumDepthSource_units sd se a' c').1

/-- Restrict the entire original secant algebra to the constructed normalized source. -/
def nodalReflectedSecantRestriction : T →ₐ[R] B :=
  IsLocalization.Away.liftAlgHom (f := j) dx (nodalReflectedSecant_unit D d e hkl a c)

omit [Module.Flat R S] in
/-- The restriction retains every function from the original input scheme. -/
theorem nodalReflectedSecantRestriction_source (v : S) :
    nodalReflectedSecantRestriction D d e hkl a c (algebraMap S T v) = algebraMap S B v :=
  IsLocalization.Away.lift_eq dx (nodalReflectedSecant_unit D d e hkl a c) v

local notation "res" => nodalReflectedSecantRestriction D d e hkl a c

omit [Module.Flat R S] in
/-- The original chord slope is exactly the returned normalized slope. -/
theorem nodalReflectedSecantRestriction_slope :
    res (dividedSecantSlope W (π ^ k) d.b3 d.b4 d.b6 a c₀) = L + algebraMap R B σ := by
  apply (nodalReflectedSecant_unit D d e hkl a c).mul_right_cancel
  have h := congrArg res (unequalDepthSecant_chord D.uniformizer_ne_zero d e hkl a c)
  simp only [map_mul, map_sub, AlgHom.commutes, AlgHom.comp_apply,
    IsScalarTower.coe_toAlgHom', nodalReflectedSecantRestriction_source] at h
  simpa only [map_sub, map_mul, AlgHom.commutes, unequalDepthRight_x,
    AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] using
    h.trans (nodalReflectedSourceSlope_relation D d e hkl a c).symm

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalFactoredSumSource
public import FLT.Mazur.WeierstrassDividedFactoredSumResidue
public import FLT.Mazur.WeierstrassDividedCommonBranchResidue
public import FLT.Mazur.WeierstrassDilatationShearVertical

/-!
# Smooth normalized sum-depth outputs beyond the wider boundary

The original node depth supplies every residue vanishing. Quadratic
quotients cancel in the constructed intercept, and returning through the
finite shear preserves the nonzero output derivative.
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
  (hkl : k ≤ l) (hm : k + 2 * l ≤ m)
  (z : Data W π (k + l))
  (a : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
  (c : Coordinate W (π ^ l) e.b3 e.b4 e.b6 →ₐ[R] S)
local notation "σ" => nodalSecondShear D k
local notation "V" => rootShearCurve W σ
local notation "sd" => (⟨d.b3, d.b4 - σ * d.b3, d.b6,
  (shearData d σ).factor3, (shearData d σ).factor4,
  (shearData d σ).factor6⟩ : Data V π k)
local notation "se" => (⟨e.b3, e.b4 - σ * e.b3, e.b6,
  (shearData e σ).factor3, (shearData e σ).factor4,
  (shearData e σ).factor6⟩ : Data V π l)
local notation "sz" => (⟨z.b3, z.b4 - σ * z.b3, z.b6,
  (shearData z σ).factor3, (shearData z σ).factor4,
  (shearData z σ).factor6⟩ : Data V π (k + l))
local notation "N" => nodalSecondShear_depth D k
local notation "b2" => nodalSecondQuotient D k
local notation "h2" => nodalSecondQuotient_factor D k
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
local notation "dd" => commonBranchData (k := k) N sd (by omega : k + 2 * k ≤ m)
local notation "ee" => commonBranchData N se hm
local notation "out" => factoredSumDepthOutput D.uniformizer_ne_zero sd se hkl dd ee sz b2 h2
  aa cc hc hd hxu i L hi hL
local notation "X" => factoredSumDepthX sd se dd ee sz b2 aa cc hc hd hxu i
local notation "Y" => factoredSumDepthY sd se dd ee sz b2 aa cc hc hd hxu i L

/-- Returning through the finite shear preserves the entire vertical derivative. -/
theorem nodalFactoredSumSourceOutput_vertical :
    nodalFactoredSumSourceOutput D d e hkl hm z a c
      (verticalDerivative W (π ^ (k + l)) z.b3 z.b4 z.b6) =
        out (verticalDerivative V (π ^ (k + l)) z.b3 (z.b4 - σ * z.b3) z.b6) := by
  dsimp only [nodalFactoredSumSourceOutput, AlgHom.comp_apply]
  rw [shearForward_verticalDerivative]

/-- Every closed-fiber field specialization beyond the sum middle has a smooth output. -/
theorem nodalFactoredSumSourceOutput_residue_vertical {K : Type u} [Field K] [Algebra R K]
    (hk : 0 < k) (hlt : k < l) (hdeep : 2 * (k + l) < m)
    (ρ : B →ₐ[R] K) (hπ0 : algebraMap R K π = 0) :
    ρ (nodalFactoredSumSourceOutput D d e hkl hm z a c
      (verticalDerivative W (π ^ (k + l)) z.b3 z.b4 z.b6)) ≠ 0 := by
  have van (b : R) (hb : b ∈ IsLocalRing.maximalIdeal R) : algebraMap R K b = 0 := by
    rw [D.maximalIdeal_eq, Ideal.mem_span_singleton] at hb
    obtain ⟨v, rfl⟩ := hb
    rw [map_mul, hπ0, zero_mul]
  have hs : algebraMap R K (π ^ k) = 0 := by
    rw [map_pow, hπ0, zero_pow (by omega)]
  have ht : algebraMap R K (π ^ (l - k)) = 0 := by
    rw [map_pow, hπ0, zero_pow (by omega)]
  have h3 := van d.b3 (Ideal.pow_le_self (by omega)
    (divided_linear_deep_mem D d (by omega)).1)
  have he3 := van e.b3 (Ideal.pow_le_self (by omega)
    (divided_linear_deep_mem D e (by omega)).1)
  obtain ⟨h4, h6⟩ := commonBranchData_residue_zero sd dd N hk (by omega) van
  obtain ⟨he4, he6⟩ := commonBranchData_residue_zero se ee N hk (by omega) van
  have hz3 := van z.b3 (Ideal.pow_le_self (by omega)
    (divided_linear_deep_mem D z (by omega)).1)
  have hz6 := van z.b6 (Ideal.pow_le_self (by omega)
    (divided_constant_exact_depth D z (by omega)).1)
  rw [nodalFactoredSumSourceOutput_vertical]
  exact factoredSumDepthOutput_residue_vertical D.uniformizer_ne_zero sd se hkl dd ee sz b2 h2
    aa cc hc hd hxu i L hi hL ρ hs ht h3 h4 h6 hz3 hz6 he3 he4 he6
    ((N).a₁_unit.map (algebraMap R K)).ne_zero

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalWiderReflectedSource
public import FLT.Mazur.WeierstrassDividedFactoredWiderReflectedResidue
public import FLT.Mazur.WeierstrassDilatationShearVertical

/-!
# Residue smoothness of the normalized wider reflected output

The finite normalization supplies the quadratic quotient. The inverse shear
preserves the vertical derivative, so the residue certificate belongs to the
original curve and the actual localized source.
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
  (hkl : k ≤ l) (hm : k + 2 * l ≤ m) (htop : m ≤ 2 * (k + l))
  (z : Data W π (m - k - l))
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
  (shearData z σ).factor6⟩ : Data V π (m - k - l))
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
local notation "out" => nodeFactoredWiderReflectedOutput N sd se hkl hm htop sz b2 h2
  aa cc hc hd hxu i L hi hL
local notation "X" => nodeFactoredWiderReflectedX N sd se hkl hm sz b2 aa cc hc hd hxu i
local notation "Y" => nodeFactoredWiderReflectedY N sd se hkl hm sz b2 aa cc hc hd hxu i L

/-- The returned output has exactly the normalized output's vertical derivative. -/
theorem nodalWiderReflectedSourceOutput_vertical :
    nodalWiderReflectedSourceOutput D d e hkl hm htop z a c
      (verticalDerivative W (π ^ (m - k - l)) z.b3 z.b4 z.b6) =
        out (verticalDerivative V (π ^ (m - k - l)) z.b3 (z.b4 - σ * z.b3) z.b6) := by
  dsimp only [nodalWiderReflectedSourceOutput, AlgHom.comp_apply]
  rw [shearForward_verticalDerivative]

/-- Smoothness survives finite normalization and return to the original chart. -/
theorem nodalWiderReflectedSourceOutput_residue_vertical {K : Type u} [Field K] [Algebra R K]
    (ρ : B →ₐ[R] K) (hs : algebraMap R K (π ^ k) = 0)
    (ht : algebraMap R K (π ^ (l - k)) = 0)
    (hv : algebraMap R K (π ^ (2 * (k + l) - m)) = 0)
    (hz3 : algebraMap R K z.b3 = 0) :
    ρ (nodalWiderReflectedSourceOutput D d e hkl hm htop z a c
      (verticalDerivative W (π ^ (m - k - l)) z.b3 z.b4 z.b6)) ≠ 0 := by
  rw [nodalWiderReflectedSourceOutput_vertical]
  exact nodeFactoredWiderReflectedOutput_residue_vertical N sd se hkl hm htop sz b2 h2
    aa cc hc hd hxu i L hi hL ρ hs ht hv hz3
    ((N).a₁_unit.map (algebraMap R K)).ne_zero

end FLT.Mazur.WeierstrassDividedDepth

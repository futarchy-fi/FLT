/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFactoredReflectedSecantResidue
public import FLT.Mazur.WeierstrassDividedNodalReflectedCoverage

/-!
# Equal-depth residue smoothness on the normalized secant source

Both ordinates vanish at positive residual depth, so the actual secant
output is smooth without a strict gap between the two input depths.
The secant source still excludes coincident abscissae.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
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
local notation "out" => nodeFactoredReflectedOutput N sd se hkl hl hm sz b2 h2
  aa cc hc hd hxu i L hi hL
local notation "X" => nodeFactoredReflectedX N sd se hkl hl b2 aa cc hc hd hxu i
local notation "Y" => nodeFactoredReflectedY N sd se hkl hl sz b2 aa cc hc hd hxu i L

/-- Smoothness survives finite normalization and return to the original chart. -/
theorem nodalReflectedSourceOutput_secant_residue_vertical {K : Type u} [Field K] [Algebra R K]
    (ρ : B →ₐ[R] K) (hs : algebraMap R K (π ^ k) = 0)
    (hv : algebraMap R K (π ^ (m - 2 * l)) = 0)
    (he3 : algebraMap R K e.b3 = 0) (hz3 : algebraMap R K z.b3 = 0) :
    ρ (nodalReflectedSourceOutput D d e hkl hl hm z a c
      (verticalDerivative W (π ^ (m - k - l)) z.b3 z.b4 z.b6)) ≠ 0 := by
  rw [nodalReflectedSourceOutput_vertical]
  exact nodeFactoredReflectedOutput_secant_residue_vertical N sd se hkl hl hm sz b2 h2
    aa cc hc hd hxu i L hi hL ρ hs hv he3 hz3
    ((N).a₁_unit.map (algebraMap R K)).ne_zero

/-- Reindexing preserves the residue certificate without a strict input-depth gap. -/
theorem nodalReflectedSourceOutputAt_secant_residue_vertical
    {r : ℕ} (w : Data W π r) (hr : r = m - k - l)
    {K : Type u} [Field K] [Algebra R K] (ρ : B →ₐ[R] K)
    (hs : algebraMap R K (π ^ k) = 0)
    (hv : algebraMap R K (π ^ (m - 2 * l)) = 0)
    (he3 : algebraMap R K e.b3 = 0) (hw3 : algebraMap R K w.b3 = 0) :
    ρ (nodalReflectedSourceOutputAt d e a c D hkl hl hm w hr
      (verticalDerivative W (π ^ r) w.b3 w.b4 w.b6)) ≠ 0 := by
  subst r
  exact nodalReflectedSourceOutput_secant_residue_vertical D d e hkl hl hm w a c
    ρ hs hv he3 hw3

variable [IsBezout R] [IsNoetherianRing R] {n : ℕ}
  (data : (idx : Fin (n + 1)) → Data W π (0 + idx.val)) (htarget : m - k - l ≤ n)
local notation "w" => data ⟨m - k - l, Nat.lt_succ_of_le htarget⟩
local notation "U" => nodalReflectedSmoothOpen D d e hkl data htarget hl hm a c

/-- All closed-fiber points of the actual source have smooth reflected-depth outputs. -/
theorem nodalReflectedSmoothOpen_secant_closed_mem (hk : 0 < k)
    (hltm : 2 * l < m) (p : PrimeSpectrum B)
    (hp : algebraMap R B π ∈ p.asIdeal) : p ∈ U := by
  let K := p.asIdeal.ResidueField
  let ρ : B →ₐ[R] K := IsScalarTower.toAlgHom R B K
  have van (b : R) (hb : b ∈ maximalIdeal R) : algebraMap R K b = 0 := by
    rw [D.maximalIdeal_eq, Ideal.mem_span_singleton] at hb
    obtain ⟨v, hv⟩ := hb
    rw [IsScalarTower.algebraMap_apply R B K]
    apply Ideal.algebraMap_residueField_eq_zero.mpr
    rw [hv, map_mul]
    exact p.asIdeal.mul_mem_right _ hp
  have hπ0 : algebraMap R K π = 0 :=
    van π (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)
  have hs : algebraMap R K (π ^ k) = 0 := by
    rw [map_pow, hπ0, zero_pow (by omega)]
  have hv : algebraMap R K (π ^ (m - 2 * l)) = 0 := by
    rw [map_pow, hπ0, zero_pow (by omega)]
  have he3 := van e.b3 (Ideal.pow_le_self (by omega)
    (divided_linear_deep_mem D e (by omega)).1)
  have hz3 := van (w).b3 (Ideal.pow_le_self (by
    change m + 1 - (0 + (m - k - l)) ≠ 0
    omega) (divided_linear_deep_mem D w (by
      change 0 + (m - k - l) ≤ m + 1
      omega)).1)
  have hn := nodalReflectedSourceOutputAt_secant_residue_vertical D d e hkl hl hm a c w
    (Nat.zero_add _) ρ hs hv he3 hz3
  apply nodalReflectedSmoothOpen_mem D d e hkl data htarget hl hm a c p
  exact fun h => hn (Ideal.algebraMap_residueField_eq_zero.mpr h)

/-- The resulting closed-fiber outputs belong to an open of the full original input scheme. -/
theorem nodalReflectedDomain_secant_closed_image (hk : 0 < k)
    (hltm : 2 * l < m) (p : PrimeSpectrum B)
    (hp : algebraMap R B π ∈ p.asIdeal) :
    PrimeSpectrum.comap (algebraMap S B) p ∈
      nodalReflectedDomain D d e hkl data htarget hl hm a c :=
  nodalReflectedDomain_image D d e hkl data htarget hl hm a c p
    (nodalReflectedSmoothOpen_secant_closed_mem D d e hkl hl hm a c data htarget hk hltm p hp)

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalLowerOutput
public import FLT.Mazur.WeierstrassDividedTangentLowerOutputResidue

/-!
# Smooth shallow nodal outputs

At depth m - 2k the terminal constant quotient is a unit. All other
required residue vanishings follow from the original node conditions,
the smaller target depth, and a normalized second coefficient.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsLocalRing R] [Module.Flat R S] {W : WeierstrassCurve R} {π : R} {m k : ℕ}
  (D : SplitNodeDepth W π m) (d : Data W π k) (hdepth : 2 * k ≤ m)
  (hm : m ≤ 3 * k) (e : Data W π (m - 2 * k))
  (a2 : R) (h2 : W.a₂ = π ^ (m - 2 * k) * a2)
  (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "s" => π ^ k
local notation "t" => π ^ (m - 2 * k)
local notation "w" => π ^ (k - (m - 2 * k))
local notation "B" => DividedTangentBranchRing W s d.b3 d.b4 d.b6 a c
local notation "ht" => isRegular_iff_ne_zero.mpr (pow_ne_zero _ D.uniformizer_ne_zero)
local notation "hs" => nodalLower_scale_factor (π := π) hm
local notation "b4'" => nodalLowerFourth D d hdepth
local notation "b6'" => nodalLowerConstant D d hdepth
local notation "h4'" => nodalLowerFourth_factor D d hdepth
local notation "h6'" => nodalLowerConstant_factor D d hdepth

local notation "out" => nodalLowerOutput D d hdepth hm e a2 h2 a c

/-- Every nodal specialization of the actual shallow output has unit vertical derivative. -/
theorem nodalLowerOutput_specialized_vertical
    (hlo : 2 * k < m) (hhi : m < 3 * k) (ha2 : a2 ∈ IsLocalRing.maximalIdeal R)
    {K : Type*} [CommRing K] (f : B →+* K) (hf : f (algebraMap R B π) = 0) :
    IsUnit (f (out (verticalDerivative W t e.b3 e.b4 e.b6))) := by
  have vanish {z : R} (hz : z ∈ IsLocalRing.maximalIdeal R) :
      f (algebraMap R B z) = 0 := by
    rw [D.maximalIdeal_eq, Ideal.mem_span_singleton] at hz
    obtain ⟨v, hv⟩ := hz
    rw [hv, map_mul, map_mul, hf, zero_mul]
  have h30 := (nodalDepth_linear_mem D.uniformizer_ne_zero D.maximalIdeal_eq
    d hdepth D.a₃_mem D.a₄_mem).1
  have he30 := (nodalDepth_linear_mem D.uniformizer_ne_zero D.maximalIdeal_eq
    e (by omega) D.a₃_mem D.a₄_mem).1
  exact dividedTangentLowerOutput_specialized_vertical W s d.b3 d.b4 d.b6 a c
    t w a2 b4' b6' e.b3 e.b4 e.b6 ht hs h2 d.factor3 d.factor4 d.factor6
    h4' h6' e.factor3 e.factor4 e.factor6 f
    (by rw [map_pow, map_pow, hf, zero_pow (by omega : m - 2 * k ≠ 0)])
    (nodalLower_scale_zero hhi (f.comp (algebraMap R B)) hf)
    (vanish h30) (vanish ha2) (vanish (nodalLowerFourth_mem D d hdepth))
    (vanish he30) (((nodalLowerConstant_isUnit D d hdepth).map (algebraMap R B)).map f)

/-- Every nodal point belongs to the actual shallow output's derivative open. -/
theorem nodalLowerOutput_nodal_mem
    (hlo : 2 * k < m) (hhi : m < 3 * k) (ha2 : a2 ∈ IsLocalRing.maximalIdeal R)
    (p : PrimeSpectrum B) (hp : algebraMap R B π ∈ p.asIdeal) :
    p ∈ PrimeSpectrum.basicOpen (out (verticalDerivative W t e.b3 e.b4 e.b6)) := by
  have hv := nodalLowerOutput_specialized_vertical D d hdepth hm e a2 h2 a c hlo hhi ha2
    (Ideal.Quotient.mk p.asIdeal) (Ideal.Quotient.eq_zero_iff_mem.mpr hp)
  change out (verticalDerivative W t e.b3 e.b4 e.b6) ∉ p.asIdeal
  intro he
  exact hv.ne_zero (Ideal.Quotient.eq_zero_iff_mem.mpr he)

end FLT.Mazur.WeierstrassDividedDepth

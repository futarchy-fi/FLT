/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFactoredDepthBranchOutput
public import FLT.Mazur.WeierstrassDividedTangentBranchDeeperSmooth
public import FLT.Mazur.WeierstrassDividedExactCoefficientDepth
public import FLT.Mazur.WeierstrassDividedVerticalSmooth

/-!
# Actual doubled-depth branch outputs are smooth beyond quadruple node depth

Exact node depth makes all three doubled coefficients vanish on the closed
fiber. The constructed second output then has a unit vertical derivative,
without further division or an assumed smoothness certificate.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {m k l : ℕ}
  (D : SplitNodeDepth W π m)
  (d : Data W π k) (e : Data W π l) (hl : l = k + k)
  (a2 : R) (h2 : W.a₂ = π ^ k * a2)
  (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "hπ" => D.uniformizer_ne_zero
local notation "s" => π ^ k
local notation "B" => DividedTangentBranchRing W s d.b3 d.b4 d.b6 a c

local notation "h3'" => branch_available_factor3 hπ d e hl
local notation "h4'" => branch_available_factor4 hπ d e hl
local notation "h6'" => branch_available_factor6 hπ d e hl
local notation "X₂" => dividedTangentBranchDeeperX W s d.b3 d.b4 d.b6 a c
  a2 e.b4 (s * e.b6) h2 h4' h6' e.b3 e.b6 h3' rfl
local notation "Y₂" => dividedTangentBranchDeeperY W s d.b3 d.b4 d.b6 a c
  a2 e.b4 (s * e.b6) h2 h4' h6' e.b3 e.b6 h3' rfl
variable [Module.Flat R S]
local notation "hs" => isRegular_iff_ne_zero.mpr (pow_ne_zero k hπ)

local notation "out" => factoredDepthBranchOutput hπ d e hl a2 h2 a c

/-- The actual doubled-depth output has a unit vertical derivative at every nodal specialization. -/
theorem nodalDoubledBranchOutput_vertical_unit (hk : 0 < k) (hm : 4 * k < m)
    {K : Type*} [CommRing K] (f : B →+* K) (hf : f (algebraMap R B π) = 0) :
    IsUnit (f (out (verticalDerivative W (π ^ l) e.b3 e.b4 e.b6))) := by
  have kill (z : R) (hz : z ∈ IsLocalRing.maximalIdeal R) :
      f (algebraMap R B z) = 0 := by
    rw [D.maximalIdeal_eq, Ideal.mem_span_singleton] at hz
    obtain ⟨v, hv⟩ := hz
    simp only [hv, map_mul, hf, zero_mul]
  have hlin := divided_linear_deep_mem D e (by omega)
  have h30 := kill e.b3 (Ideal.pow_le_self (by omega) hlin.1)
  have h40 := kill e.b4 (Ideal.pow_le_self (by omega) hlin.2)
  have h60 := kill e.b6 (Ideal.pow_le_self (by omega)
    (divided_constant_exact_depth D e (by omega)).1)
  have hs0 : f (algebraMap R B s) = 0 := by
    simp only [map_pow, hf, zero_pow (Nat.ne_of_gt hk)]
  rw [verticalDerivative_eq]
  simp only [map_add, map_mul, map_ofNat, AlgHom.commutes,
    factoredDepthBranchOutput_x, factoredDepthBranchOutput_y]
  simpa only [map_add, map_mul, map_ofNat] using
    dividedTangentBranchDeeper_specialized_vertical W s d.b3 d.b4 d.b6 a c
      a2 e.b4 (s * e.b6) h2 h4' h6' e.b3 e.b6 h3' rfl hs
      d.factor3 d.factor4 d.factor6 f hs0 h30 h40 h60

/-- Every closed-fiber point is in the derivative open of the constructed doubled output. -/
theorem nodalDoubledBranchOutput_vertical_mem (hk : 0 < k) (hm : 4 * k < m)
    (p : PrimeSpectrum B) (hp : algebraMap R B π ∈ p.asIdeal) :
    p ∈ PrimeSpectrum.basicOpen (out (verticalDerivative W (π ^ l) e.b3 e.b4 e.b6)) := by
  let f : B →+* B ⧸ p.asIdeal := Ideal.Quotient.mk p.asIdeal
  have hu := nodalDoubledBranchOutput_vertical_unit D d e hl a2 h2 a c hk hm f
    (Ideal.Quotient.eq_zero_iff_mem.mpr hp)
  intro he
  exact hu.ne_zero (Ideal.Quotient.eq_zero_iff_mem.mpr he)

end FLT.Mazur.WeierstrassDividedDepth

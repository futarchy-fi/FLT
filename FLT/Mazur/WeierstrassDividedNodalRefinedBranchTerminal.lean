/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNodalBranchTerminalConstant
public import FLT.Mazur.WeierstrassDividedNodalRefinedBranchOutput
public import FLT.Mazur.WeierstrassDividedTangentBranchRefinedResidue
public import FLT.Mazur.WeierstrassDividedVerticalSmooth

/-!
# Smooth intermediate outputs below quadruple node depth

At the full residual refinement r = m - 3k < k, cancellation of the
regular refinement scale exposes a unit terminal constant. The output's
actual vertical derivative is a unit at every nodal specialization.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsDomain R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {m k r : ℕ}
  (D : SplitNodeDepth W π m) (d : Data W π k) (hdepth : 3 * k ≤ m)
  (hrk : r ≤ k) (hrm : r ≤ m - 3 * k) (e : Data W π (k + r))
  (a2 : R) (h2 : W.a₂ = π ^ k * a2)
  (a c : Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "s" => π ^ k
local notation "t" => π ^ r
local notation "B" => DividedTangentBranchRing W s d.b3 d.b4 d.b6 a c
local notation "hπ" => D.uniformizer_ne_zero
local notation "b4'" => nodalBranchFourth D d hdepth
local notation "b6'" => nodalBranchConstant D d hdepth
local notation "h4'" => nodalBranchFourth_factor D d hdepth
local notation "h6'" => nodalBranchConstant_factor D d hdepth
local notation "hts" => pow_dvd_pow π hrk
local notation "ht3" => nodalBranchRefinement_third_dvd D d hdepth hrk
local notation "ht6" => nodalBranchRefinement_constant_dvd D d hdepth hrm

variable [Module.Flat R S]
local notation "out" => nodalRefinedBranchOutput D d hdepth hrk hrm e a2 h2 a c

/-- The actual refined map evaluates the vertical derivative at its constructed coordinates. -/
theorem nodalRefinedBranchOutput_vertical :
    out (verticalDerivative W (π ^ (k + r)) e.b3 e.b4 e.b6) =
      2 * dividedTangentBranchRefinedY W s d.b3 d.b4 d.b6 a c
          a2 b4' b6' h2 h4' h6' t hts ht3 ht6 +
        algebraMap R B W.a₁ * dividedTangentBranchRefinedX W s d.b3 d.b4 d.b6 a c
          a2 b4' b6' h2 h4' h6' t hts ht3 ht6 + algebraMap R B e.b3 := by
  rw [verticalDerivative_eq]
  simp only [map_add, map_mul, map_ofNat, AlgHom.commutes,
    nodalRefinedBranchOutput_x, nodalRefinedBranchOutput_y]

/-- Every nodal residue of a fully refined intermediate output has a unit vertical derivative. -/
theorem nodalRefinedBranchOutput_terminal_vertical
    (hm : m < 4 * k) (hr : r = m - 3 * k)
    {T : Type*} [CommRing T] (f : B →+* T) (hf : f (algebraMap R B π) = 0) :
    IsUnit (f (out (verticalDerivative W (π ^ (k + r)) e.b3 e.b4 e.b6))) := by
  rw [nodalRefinedBranchOutput_vertical]
  have hw : s = t * π ^ (k - r) := by
    rw [hr]
    exact nodalBranchIntermediate_scale_factor hm
  have hb : b6' = t * nodalBranchTerminalConstant D d hdepth := by
    rw [hr]
    exact nodalBranchTerminalConstant_factor D d hdepth
  have hw0 : f (algebraMap R B (π ^ (k - r))) = 0 := by
    rw [hr]
    exact nodalBranchIntermediate_scale_zero hm (f.comp (algebraMap R B)) hf
  have hc3 : f (algebraMap R B e.b3) = 0 := by
    have hmem := (nodalDepth_linear_mem D.uniformizer_ne_zero D.maximalIdeal_eq
      e (by omega) D.a₃_mem D.a₄_mem).1
    rw [D.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
    obtain ⟨z, hz⟩ := hmem
    rw [hz, map_mul, map_mul, hf, zero_mul]
  exact dividedTangentBranchRefined_specialized_vertical W s d.b3 d.b4 d.b6 a c
    a2 b4' b6' h2 h4' h6' t hts ht3 ht6
    (isRegular_iff_ne_zero.mpr (pow_ne_zero k hπ))
    (nodalBranchRefinement_third_dvd D d hdepth (le_refl k))
    (π ^ (k - r)) (nodalBranchTerminalConstant D d hdepth) hw hb f hw0
    (((nodalBranchTerminalConstant_isUnit D d hdepth).map (algebraMap R B)).map f) e.b3 hc3

/-- The complete nodal branch fiber lies in the actual intermediate derivative open. -/
theorem nodalRefinedBranchOutput_terminal_mem
    (hm : m < 4 * k) (hr : r = m - 3 * k)
    (p : PrimeSpectrum B) (hp : algebraMap R B π ∈ p.asIdeal) :
    p ∈ PrimeSpectrum.basicOpen (out (verticalDerivative W (π ^ (k + r))
      e.b3 e.b4 e.b6)) := by
  let f : B →+* B ⧸ p.asIdeal := Ideal.Quotient.mk p.asIdeal
  have hv := nodalRefinedBranchOutput_terminal_vertical D d hdepth hrk hrm e a2 h2 a c
    hm hr f (Ideal.Quotient.eq_zero_iff_mem.mpr hp)
  change out (verticalDerivative W (π ^ (k + r)) e.b3 e.b4 e.b6) ∉ p.asIdeal
  intro he
  exact hv.ne_zero (Ideal.Quotient.eq_zero_iff_mem.mpr he)

end FLT.Mazur.WeierstrassDividedDepth

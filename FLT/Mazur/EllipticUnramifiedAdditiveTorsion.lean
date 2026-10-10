/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticShortUnramifiedTorsion
public import FLT.Mazur.EllipticComponentVariableChange

/-!
# Additive smooth torsion at the residue prime

An integral short-normal-form change preserves both additive invariants and
smooth reduction of the exact original point. The short scaling obstruction
therefore excludes nonzero smooth prime torsion on every additive equation
over a complete unramified DVR at a prime at least seventeen.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {K : Type*} [Field K] (A : ValuationSubring K)
  [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A]

/-- Additive smooth prime torsion vanishes at a large unramified residue prime. -/
theorem smooth_prime_torsion_eq_zero_of_additive_unramified
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p]
    (hp : Irreducible (p : A)) (hp17 : 17 ≤ p)
    (W : WeierstrassCurve A) [(W.map (algebraMap A K)).IsElliptic]
    (hd : W.Δ ∈ maximalIdeal A) (hc : W.c₄ ∈ maximalIdeal A)
    (P : (W.map (algebraMap A K)).toProjective.Point) (hP : p • P = 0)
    (hsm : SmoothReduction A W P) : P = 0 := by
  classical
  obtain ⟨h2, h3⟩ := two_three_units_of_residue_char_gt_three (R := A) p (by omega)
  let _ : Invertible (2 : A) := h2.invertible
  let _ : Invertible (3 : A) := h3.invertible
  let C := W.toShortNF
  let V := C • W
  let e := integralProjectiveVariableChange A W C
  have hΔ : W.Δ ≠ 0 := by
    intro hz
    have hu := (W.map (algebraMap A K)).isUnit_Δ
    rw [map_Δ, hz, map_zero] at hu
    exact not_isUnit_zero hu
  have hv : V.Δ ≠ 0 := by
    rw [show V.Δ = (↑(C.u⁻¹) : A) ^ 12 * W.Δ from variableChange_Δ W C]
    exact mul_ne_zero (pow_ne_zero 12 (Units.ne_zero _)) hΔ
  have hvd : V.Δ ∈ maximalIdeal A := by
    rw [show V.Δ = (↑(C.u⁻¹) : A) ^ 12 * W.Δ from variableChange_Δ W C]
    exact (maximalIdeal A).mul_mem_left _ hd
  have hvc : V.c₄ ∈ maximalIdeal A := by
    rw [show V.c₄ = (↑(C.u⁻¹) : A) ^ 4 * W.c₄ from variableChange_c₄ W C]
    exact (maximalIdeal A).mul_mem_left _ hc
  have hn : p • e.symm P = 0 := by rw [← map_nsmul, hP, map_zero]
  have hs : SmoothReduction A V (e.symm P) := by
    apply (integralProjectiveVariableChange_smooth A W C _).mp
    simpa only [show integralProjectiveVariableChange A W C = e from rfl,
      AddEquiv.apply_symm_apply] using hsm
  have hz := short_smooth_prime_torsion_eq_zero_unramified A p hp hp17 V hv hvd hvc
    (e.symm P) hn hs
  exact e.symm.injective (hz.trans (map_zero e.symm).symm)

end FLT.Mazur

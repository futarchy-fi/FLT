/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicUniformResidualDiscrepancy
public import FLT.Mazur.NilpotentTorsionPowerEquality
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Uniform full residual congruences at every positive integer modulus

For each positive modulus, one positive exponent makes every finite fixed
function satisfy the full residual relation modulo that modulus. This is an
unconditional assertion about the original arrow ring, including prime-power
thickenings. Congruence at each modulus is not asserted to imply exact equality.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (i : InvariantAffineIndex n)

/-- Every positive modulus has a uniform power making all finite invariants fully congruent. -/
theorem affineRelabel_uniform_power_congruence (m : ℕ) (hm : 0 < m) :
    ∃ e : ℕ, 0 < e ∧ ∀ s : affineRelabelSections n i,
      (affineResidualSource n i).appTop (s.val ^ e) -
        (affineResidualTarget n i).appTop (s.val ^ e) ∈
      Ideal.span {(m : Γ((affineResidualDomain n i).toScheme, ⊤))} := by
  let D := Γ((affineResidualDomain n i).toScheme, ⊤)
  let J : Ideal D := Ideal.span {(m : D)}
  let q := Ideal.Quotient.mk J
  let I := (affineRelabelDiscrepancyIdeal n i).map q
  have hI : IsNilpotent I :=
    (affineRelabelDiscrepancyIdeal_isNilpotent n i).map (Ideal.mapHom q)
  have hmzero : (m : D ⧸ J) = 0 := by
    rw [← map_natCast q]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  obtain ⟨e, he, h⟩ := NilpotentTorsionPowerEquality.exists_uniform_power hm hI
    (fun z _ => by rw [hmzero, zero_mul])
  refine ⟨e, he, fun s => ?_⟩
  have hs : q ((affineResidualSource n i).appTop s.val) -
      q ((affineResidualTarget n i).appTop s.val) ∈ I := by
    rw [← map_sub]
    exact Ideal.mem_map_of_mem q (affineRelabelDiscrepancy_mem n i s)
  have hh := h _ _ hs
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q (_ - _) = 0
  rw [map_sub, map_pow, map_pow, map_pow, map_pow, hh, sub_self]

end FLT.Mazur.CyclicCharacteristicOrbit

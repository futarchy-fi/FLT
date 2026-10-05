/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorStalkLength
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.OrderOfVanishing.Basic

/-!
# Additivity and finiteness of Cartier multiplicities

Multiplying Cartier ideals adds the lengths of their quotient stalks, and
powers multiply lengths. At points of codimension at most one on a locally
Noetherian scheme these lengths are finite, including on nonreduced schemes.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.FCurve

open AnnihilatorSubsheaf

variable {X : Scheme.{u}} {I J : X.IdealSheafData}

/-- The actual ideal stalk commutes with multiplication of ideal sheaves. -/
theorem stalkIdeal_mul (I J : X.IdealSheafData) (x : X) :
    stalkIdeal (I * J) x = stalkIdeal I x * stalkIdeal J x := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x)
      TopologicalSpace.isOpen_univ
  rw [stalkIdeal_eq_map (I * J) x ⟨U, hU⟩ hx,
    stalkIdeal_eq_map I x ⟨U, hU⟩ hx, stalkIdeal_eq_map J x ⟨U, hU⟩ hx]
  exact Ideal.map_mul _ _ _

/-- Cartier multiplicities add under multiplication of the actual divisor ideals. -/
theorem EffectiveCartier.stalkLength_mul (hI : EffectiveCartier I)
    (hJ : EffectiveCartier J) (x : X) :
    divisorStalkLength (I * J) x = divisorStalkLength I x + divisorStalkLength J x := by
  obtain ⟨a, _, hIa⟩ := hI.stalk_generator x
  obtain ⟨b, hb, hJb⟩ := hJ.stalk_generator x
  have hIJ : stalkIdeal (I * J) x = Ideal.span {a * b} := by
    rw [stalkIdeal_mul, hIa, hJb, Ideal.span_singleton_mul_span_singleton]
  rw [divisorStalkLength_eq_length_quotient _ _ _ hIJ,
    divisorStalkLength_eq_length_quotient _ _ _ hIa,
    divisorStalkLength_eq_length_quotient _ _ _ hJb]
  exact Ring.ord_mul _ hb.mem_nonZeroDivisors

/-- The empty divisor has zero multiplicity everywhere. -/
theorem divisorStalkLength_one (x : X) :
    divisorStalkLength (1 : X.IdealSheafData) x = 0 := by
  rw [divisorStalkLength_eq_zero_iff]
  exact fun h ↦ h

/-- Repeated Cartier divisors retain all multiplicities. -/
theorem EffectiveCartier.stalkLength_pow (hI : EffectiveCartier I) (n : ℕ) (x : X) :
    divisorStalkLength (I ^ n) x = n • divisorStalkLength I x := by
  induction n with
  | zero => rw [pow_zero, zero_nsmul, divisorStalkLength_one]
  | succ n hn => rw [pow_succ, (hI.pow n).stalkLength_mul hI, hn, add_nsmul, one_nsmul]

/-- A regular equation on a Noetherian stalk of dimension at most one has finite length. -/
theorem EffectiveCartier.stalkLength_ne_top [IsLocallyNoetherian X]
    (hI : EffectiveCartier I) (x : X) (hx : Order.coheight x ≤ 1) :
    divisorStalkLength I x ≠ ⊤ := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx
  obtain ⟨a, ha, hIa⟩ := hI.stalk_generator x
  rw [divisorStalkLength_eq_length_quotient I x a hIa]
  exact Ring.ord_ne_top ha.mem_nonZeroDivisors

/-- Under the curve hypotheses, support is detected by a positive natural multiplicity. -/
theorem EffectiveCartier.stalkLength_toNat_pos_iff [IsLocallyNoetherian X]
    (hI : EffectiveCartier I) (x : X) (hx : Order.coheight x ≤ 1) :
    0 < (divisorStalkLength I x).toNat ↔ x ∈ I.support := by
  rw [← divisorStalkLength_pos_iff]
  exact ⟨fun h ↦ pos_iff_ne_zero.mpr (fun hz ↦ by simp [hz] at h),
    fun h ↦ ENat.toNat_pos h.ne' (hI.stalkLength_ne_top x hx)⟩

end FLT.Mazur.FCurve

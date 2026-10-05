/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierIdealStalkDescent
public import Mathlib.RingTheory.Length

/-!
# Quotient-stalk length and divisor support

The multiplicity used here is the length of the actual structure stalk modulo
the actual ideal stalk. It detects support even when the length is infinite.
No finite-length or curve-degree assertion is built into the definition.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.FCurve

open AnnihilatorSubsheaf

variable {X Y : Scheme.{u}}

/-- The quotient-stalk length of a closed subscheme at an ambient point. -/
def divisorStalkLength (I : X.IdealSheafData) (x : X) : ℕ∞ :=
  Module.length (X.presheaf.stalk x) (X.presheaf.stalk x ⧸ stalkIdeal I x)

/-- Membership in the geometric support means the actual ideal stalk is proper. -/
theorem mem_support_iff_stalkIdeal_ne_top (I : X.IdealSheafData) (x : X) :
    x ∈ I.support ↔ stalkIdeal I x ≠ ⊤ := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x)
      TopologicalSpace.isOpen_univ
  rw [I.mem_support_iff_of_mem (U := ⟨U, hU⟩) hx, X.mem_zeroLocus_iff,
    stalkIdeal_eq_map I x ⟨U, hU⟩ hx]
  constructor
  · intro h
    apply ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    exact (IsLocalRing.mem_maximalIdeal _).mpr
      (fun hu ↦ h a ha ((X.mem_basicOpen' a ⟨x, hx⟩).mpr hu))
  · intro h a ha hu
    exact h ((I.ideal ⟨U, hU⟩).map (X.presheaf.germ U x hx).hom |>.eq_top_of_isUnit_mem
      (Ideal.mem_map_of_mem _ ha) ((X.mem_basicOpen' a ⟨x, hx⟩).mp hu))

/-- Positive local length detects precisely the support, without a finiteness assumption. -/
theorem divisorStalkLength_pos_iff (I : X.IdealSheafData) (x : X) :
    0 < divisorStalkLength I x ↔ x ∈ I.support := by
  rw [divisorStalkLength, Module.length_pos_iff, Ideal.Quotient.nontrivial_iff,
    mem_support_iff_stalkIdeal_ne_top]

/-- Local length vanishes exactly off the support. -/
theorem divisorStalkLength_eq_zero_iff (I : X.IdealSheafData) (x : X) :
    divisorStalkLength I x = 0 ↔ x ∉ I.support := by
  rw [← divisorStalkLength_pos_iff, not_lt, le_zero_iff]

/-- A regular local equation computes the intrinsic quotient-stalk length. -/
theorem divisorStalkLength_eq_length_quotient (I : X.IdealSheafData) (x : X)
    (a : X.presheaf.stalk x) (ha : stalkIdeal I x = Ideal.span {a}) :
    divisorStalkLength I x =
      Module.length (X.presheaf.stalk x) (X.presheaf.stalk x ⧸ Ideal.span {a}) := by
  rw [divisorStalkLength, ha]

/-- Every Cartier divisor has a regular equation computing its local length. -/
theorem EffectiveCartier.exists_stalkLength_equation {I : X.IdealSheafData}
    (hI : EffectiveCartier I) (x : X) :
    ∃ a : X.presheaf.stalk x, IsRegular a ∧
      divisorStalkLength I x =
        Module.length (X.presheaf.stalk x) (X.presheaf.stalk x ⧸ Ideal.span {a}) := by
  obtain ⟨a, ha, hIa⟩ := hI.stalk_generator x
  exact ⟨a, ha, divisorStalkLength_eq_length_quotient I x a hIa⟩

/-- Arbitrary pullback preserves whether the local length is positive. -/
theorem divisorStalkLength_comap_pos_iff (I : X.IdealSheafData) (f : Y ⟶ X) (y : Y) :
    0 < divisorStalkLength (I.comap f) y ↔ 0 < divisorStalkLength I (f y) := by
  simp only [divisorStalkLength_pos_iff, Scheme.IdealSheafData.support_comap]
  rfl

end FLT.Mazur.FCurve

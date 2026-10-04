/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.TwoExtensionDeflation

/-!
# Ordinary boundary descent through a normal quotient

A normalized bounding cochain that vanishes on the subgroup is constant
on quotient fibers and takes subgroup-invariant values.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable {k G : Type} [CommRing k] [Group G] (M : Rep k G)
  (N : Subgroup G) [N.Normal]

local notation "MQ" => M.quotientToInvariants N
local notation "q" => QuotientGroup.mk' N

variable (c : (G ⧸ N) × (G ⧸ N) → M.quotientToInvariants N) (b : G → M)
  (hb : ∀ g h, M.ρ g (b h) - b (g * h) + b g =
    (c (QuotientGroup.mk' N g, QuotientGroup.mk' N h)).val)
  (hbN : ∀ n : N, b n = 0)
  (hc0 : ∀ g, c (g, 1) = 0) (hc1 : ∀ g, c (1, g) = 0)

include hb hbN hc0 in
/-- A normalized bounding cochain is constant on quotient fibers. -/
theorem quotientBoundary_fiber (g h : G) (he : q g = q h) : b g = b h := by
  have hn : g⁻¹ * h ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (g⁻¹ * h) = 1
    rw [map_mul, map_inv, he, inv_mul_cancel]
  have hx := hb g (g⁻¹ * h)
  have hq : q (g⁻¹ * h) = 1 := (QuotientGroup.eq_one_iff _).mpr hn
  rw [hq, hc0, hbN ⟨_, hn⟩, map_zero, mul_inv_cancel_left] at hx
  rw [zero_sub] at hx
  exact (neg_add_eq_zero.mp hx).symm

include hb hbN hc0 hc1 in
/-- Every value of a normalized bounding cochain is subgroup-invariant. -/
theorem quotientBoundary_fixed (g : G) (n : N) : M.ρ (n : G) (b g) = b g := by
  have hn : q (n : G) = 1 := (QuotientGroup.eq_one_iff _).mpr n.property
  have h := hb n g
  rw [hn, hc1, hbN n, add_zero] at h
  have he : q ((n : G) * g) = q g := by rw [map_mul, hn, one_mul]
  exact (sub_eq_zero.mp h).trans (quotientBoundary_fiber M N c b hb hbN hc0 _ _ he)

include hb hbN hc0 hc1 in
/-- A normalized bounding cochain descends to an actual quotient one-cochain. -/
theorem quotientBoundary_descends : ∃ d : (G ⧸ N) → MQ, d₁₂ MQ d = c := by
  let d : (G ⧸ N) → MQ := fun a =>
    ⟨b a.out, quotientBoundary_fixed M N c b hb hbN hc0 hc1 a.out⟩
  have hd (g : G) : (d (q g)).val = b g :=
    quotientBoundary_fiber M N c b hb hbN hc0 _ _ (QuotientGroup.out_eq' _)
  refine ⟨d, ?_⟩
  funext a
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective N a.1
  obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective N a.2
  obtain rfl : a = (q g, q h) := Prod.ext hg.symm hh.symm
  apply Subtype.ext
  change M.ρ g (d (q h)).val - (d (q g * q h)).val + (d (q g)).val = _
  rw [← map_mul, hd, hd, hd]
  exact hb g h

end LocalClassFieldTheory

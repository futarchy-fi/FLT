/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Regular.ParameterFirstRegular

/-! # Parameter lists at full depth are regular -/

@[expose] public section

universe u

namespace RingTheory.Sequence

open IsLocalRing
open scoped Pointwise

variable {R M : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]

omit [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R M] [Nontrivial M] in
/-- Passing to a parameter quotient retains the Artinian terminal quotient condition. -/
theorem isArtinianRing_parameter_quotSMulTop (x : R) (rs : List R)
    [IsArtinianRing (R ⧸ (Module.annihilator R M ⊔ Ideal.ofList (x :: rs)))] :
    IsArtinianRing (R ⧸ (Module.annihilator R (QuotSMulTop x M) ⊔ Ideal.ofList rs)) := by
  have hle : Module.annihilator R M ⊔ Ideal.ofList (x :: rs) ≤
      Module.annihilator R (QuotSMulTop x M) ⊔ Ideal.ofList rs := by
    apply sup_le
    · exact (LinearMap.annihilator_le_of_surjective (R := R)
        (x • (⊤ : Submodule R M)).mkQ (Submodule.mkQ_surjective _)).trans le_sup_left
    · rw [Ideal.ofList_cons]
      exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr
        ((show Module.annihilator R (QuotSMulTop x M) ≤
          Module.annihilator R (QuotSMulTop x M) ⊔ Ideal.ofList rs from le_sup_left)
          (QuotSMulTop.mem_annihilator M x))) le_sup_right
  exact (Ideal.Quotient.factor_surjective hle).isArtinianRing

/-- A parameter list is regular if some regular sequence has the same length. -/
theorem isRegular_of_artinian_quotient_of_exists_regular (rs : List R)
    (hm : ∀ r ∈ rs, r ∈ maximalIdeal R)
    [IsArtinianRing (R ⧸ (Module.annihilator R M ⊔ Ideal.ofList rs))]
    (hex : ∃ qs : List R, qs.length = rs.length ∧ IsRegular M qs) : IsRegular M rs := by
  induction rs generalizing M with
  | nil => exact IsRegular.nil R M
  | cons x rs ih =>
    have hx := isSMulRegular_parameter_head (M := M) (x := x)
      (fun r hr ↦ hm r (List.mem_cons_of_mem x hr)) hex
    have hxm := hm x List.mem_cons_self
    obtain ⟨qs, hlen, hqs⟩ := hex
    have hexQ := exists_regular_quotient_of_regular hx hxm hqs hlen
    have := nontrivial_quotSMulTop_of_mem_maximalIdeal M hxm
    have := isArtinianRing_parameter_quotSMulTop (M := M) x rs
    exact (isRegular_cons_iff M x rs).mpr
      ⟨hx, ih (fun r hr ↦ hm r (List.mem_cons_of_mem x hr)) hexQ⟩

/-- Ring form of the local parameter theorem, with depth witnessed by a regular sequence. -/
theorem isRegular_of_artinian_quotient_of_full_length (rs : List R)
    (hm : ∀ r ∈ rs, r ∈ maximalIdeal R) [IsArtinianRing (R ⧸ Ideal.ofList rs)]
    (hex : ∃ qs : List R, qs.length = rs.length ∧ IsRegular R qs) : IsRegular R rs := by
  have : IsArtinianRing (R ⧸ (Module.annihilator R R ⊔ Ideal.ofList rs)) := by
    have hAnn : Module.annihilator R R = ⊥ := Module.annihilator_eq_bot.mpr inferInstance
    rw [hAnn, bot_sup_eq]
    infer_instance
  exact isRegular_of_artinian_quotient_of_exists_regular rs hm hex

end RingTheory.Sequence

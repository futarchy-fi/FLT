/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Depth.Rees
public import Mathlib.RingTheory.KrullDimension.Regular

/-! # Depth drop under a regular element, expressed through regular sequences -/

@[expose] public section

universe u

namespace RingTheory.Sequence

open IsLocalRing CategoryTheory Abelian

variable {R M : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]

omit [IsNoetherianRing R] [Module.Finite R M] [Nontrivial M] in
/-- Elements of a regular sequence over a local ring belong to its maximal ideal. -/
theorem IsRegular.mem_maximalIdeal {rs : List R} (h : IsRegular M rs) {r : R}
    (hr : r ∈ rs) : r ∈ maximalIdeal R := by
  apply IsLocalRing.le_maximalIdeal (J := Ideal.ofList rs) _ (Ideal.subset_span hr)
  intro ht
  apply h.top_ne_smul
  simp [ht]

/-- Quotienting by any regular element lowers an available regular-sequence length by one. -/
theorem exists_regular_quotient_of_regular {x : R} (hx : IsSMulRegular M x)
    (hm : x ∈ maximalIdeal R) {n : ℕ} {rs : List R}
    (hreg : IsRegular M rs) (hlen : rs.length = n + 1) :
    ∃ qs : List R, qs.length = n ∧ IsRegular (QuotSMulTop x M) qs := by
  let I := maximalIdeal R
  let N : ModuleCat.{u} R := ModuleCat.of R (R ⧸ I)
  have hsupp : Module.support R N = PrimeSpectrum.zeroLocus I := by
    change Module.support R (R ⧸ I) = _
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
  have hlt : I • (⊤ : Submodule R M) < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    exact (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (maximalIdeal_le_jacobson _)).symm
  have hext := ModuleCat.subsingleton_ext_of_exists_isRegular I N hsupp.subset
    (ModuleCat.of R M) hlt rs (fun r hr ↦ hreg.mem_maximalIdeal hr) hreg
  have hs : (ModuleCat.smulShortComplex (ModuleCat.of R M) x).ShortExact :=
    IsSMulRegular.smulShortComplex_shortExact (M := ModuleCat.of R M) hx
  have hextQ : ∀ i < n,
      Subsingleton (CategoryTheory.Abelian.Ext N (ModuleCat.of R (QuotSMulTop x M)) i) := by
    intro i hi
    have hz₁ := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (hext i (by omega))
    have hz₂ := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (hext (i + 1) (by omega))
    exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
      ((Ext.covariant_sequence_exact₃' N hs) i (i + 1) rfl)
      (hz₁.eq_zero_of_src _) (hz₂.eq_zero_of_tgt _)
  have := nontrivial_quotSMulTop_of_mem_maximalIdeal M hm
  have hltQ : I • (⊤ : Submodule R (QuotSMulTop x M)) < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    exact (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (maximalIdeal_le_jacobson _)).symm
  obtain ⟨qs, hlen, _, hqs⟩ := ModuleCat.exists_isRegular_of_exists_subsingleton_ext
    I n (ModuleCat.of R (QuotSMulTop x M)) hltQ N hsupp hextQ
  exact ⟨qs, hlen, hqs⟩

/-- Regular-sequence existence in consecutive lengths is equivalent across a regular quotient. -/
theorem exists_regular_succ_iff_quotient {x : R} (hx : IsSMulRegular M x)
    (hm : x ∈ maximalIdeal R) (n : ℕ) :
    (∃ rs : List R, rs.length = n + 1 ∧ IsRegular M rs) ↔
      ∃ qs : List R, qs.length = n ∧ IsRegular (QuotSMulTop x M) qs := by
  constructor
  · rintro ⟨rs, hlen, hreg⟩
    exact exists_regular_quotient_of_regular hx hm hreg hlen
  · rintro ⟨qs, hlen, hreg⟩
    exact ⟨x :: qs, by simp [hlen], (isRegular_cons_iff M x qs).mpr ⟨hx, hreg⟩⟩

/-- If n+1 is the maximum regular-sequence length, the quotient has maximum length n. -/
theorem maximal_regular_length_quotient {x : R} (hx : IsSMulRegular M x)
    (hm : x ∈ maximalIdeal R) {n : ℕ}
    (hex : ∃ rs : List R, rs.length = n + 1 ∧ IsRegular M rs)
    (hmax : ∀ rs : List R, IsRegular M rs → rs.length ≤ n + 1) :
    (∃ qs : List R, qs.length = n ∧ IsRegular (QuotSMulTop x M) qs) ∧
      ∀ qs : List R, IsRegular (QuotSMulTop x M) qs → qs.length ≤ n := by
  refine ⟨(exists_regular_succ_iff_quotient hx hm n).mp hex, ?_⟩
  intro qs hqs
  have h := hmax (x :: qs) ((isRegular_cons_iff M x qs).mpr ⟨hx, hqs⟩)
  simpa using h

end RingTheory.Sequence

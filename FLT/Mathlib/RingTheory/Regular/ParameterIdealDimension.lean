/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.LocalRing.Quotient

/-! # Dimension bounds from an Artinian parameter quotient -/

@[expose] public section

namespace RingTheory.Sequence

open IsLocalRing

variable {R : Type*} [CommRing R]

/-- An Artinian parameter quotient remains Artinian after a surjective ring map. -/
theorem isArtinianRing_quotient_ofList_map {S : Type*} [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (rs : List R)
    {I : Ideal R} (hI : I ≤ RingHom.ker f)
    [IsArtinianRing (R ⧸ (I ⊔ Ideal.ofList rs))] :
    IsArtinianRing (S ⧸ Ideal.ofList (rs.map f)) := by
  have hle : Ideal.ofList rs ≤ (Ideal.ofList (rs.map f)).comap f := by
    rw [← Ideal.map_ofList]
    exact Ideal.le_comap_map
  have hsup : I ⊔ Ideal.ofList rs ≤ (Ideal.ofList (rs.map f)).comap f :=
    sup_le (hI.trans (Ideal.ker_le_comap f)) hle
  exact (Ideal.quotientMap_surjective (H := hsup) hf).isArtinianRing

variable [IsNoetherianRing R] [IsLocalRing R]

/-- A list of parameters with Artinian quotient has at least the local dimension many terms. -/
theorem ringKrullDim_le_length_of_artinian_quotient (rs : List R)
    (hm : ∀ r ∈ rs, r ∈ maximalIdeal R) [IsArtinianRing (R ⧸ Ideal.ofList rs)] :
    ringKrullDim R ≤ (rs.length : WithBot ℕ∞) := by
  classical
  have hdim : ringKrullDim (R ⧸ Ideal.ofList rs) ≤ 0 :=
    (Ring.krullDimLE_iff (n := 0)).mp inferInstance
  have hs : (Ideal.ofList rs).spanFinrank ≤ rs.length := by
    have heq : {r | r ∈ rs} = (rs.toFinset : Set R) := by ext; simp
    rw [Ideal.ofList, heq]
    exact (Submodule.spanFinrank_span_le_ncard_of_finite (R := R)
      rs.toFinset.finite_toSet).trans (by rw [Set.ncard_coe_finset]; exact List.toFinset_card_le rs)
  have hle := ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank (Ideal.ofList rs)
    (by rw [IsLocalRing.ringJacobson_eq_maximalIdeal]; exact Ideal.span_le.mpr hm)
  exact hle.trans (by simpa using add_le_add hdim (show
    ((Ideal.ofList rs).spanFinrank : WithBot ℕ∞) ≤ (rs.length : WithBot ℕ∞) by exact_mod_cast hs))

/-- If the first parameter lies in a prime, the dimension there is bounded by the tail length. -/
theorem ringKrullDim_quotient_le_parameter_tail {p : Ideal R} [p.IsPrime]
    {I : Ideal R} (hIp : I ≤ p) {x : R} {rs : List R} (hx : x ∈ p)
    (hm : ∀ r ∈ rs, r ∈ maximalIdeal R)
    [IsArtinianRing (R ⧸ (I ⊔ Ideal.ofList (x :: rs)))] :
    ringKrullDim (R ⧸ p) ≤ (rs.length : WithBot ℕ∞) := by
  have : IsLocalRing (R ⧸ p) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  have : IsLocalHom (Ideal.Quotient.mk p) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have heq : Ideal.ofList ((x :: rs).map (Ideal.Quotient.mk p)) =
      Ideal.ofList (rs.map (Ideal.Quotient.mk p)) := by
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  have : IsArtinianRing ((R ⧸ p) ⧸ Ideal.ofList (rs.map (Ideal.Quotient.mk p))) := by
    rw [← heq]
    exact isArtinianRing_quotient_ofList_map (Ideal.Quotient.mk p)
      Ideal.Quotient.mk_surjective (x :: rs) (by simpa using hIp)
  have hmem : ∀ r ∈ rs.map (Ideal.Quotient.mk p), r ∈ maximalIdeal (R ⧸ p) := by
    intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    exact map_nonunit (Ideal.Quotient.mk p) s (hm s hs)
  simpa using ringKrullDim_le_length_of_artinian_quotient _ hmem

end RingTheory.Sequence

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.Flat.NoetherianFibreRegularElement
public import FLT.Mathlib.RingTheory.Flat.RelativeQuotSMulTensor
public import Mathlib.RingTheory.Regular.RegularSequence

/-! # Lifting a fibre-regular sequence while preserving relative flatness -/

@[expose] public noncomputable section

open TensorProduct RingTheory.Sequence

namespace Module.Flat

variable {R S N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [IsNoetherianRing S] [AddCommGroup N] [Module R N] [Module S N]
  [IsScalarTower R S N] [Module.Finite S N] [Flat R N]

/-- An ordered weakly regular sequence on the residue fibre lifts to a weakly
regular sequence with base-flat quotient. -/
theorem regular_and_flat_quotient_of_fibre_sequence (rs : List S)
    (hrs : IsWeaklyRegular (N ⊗[R] (R ⧸ IsLocalRing.maximalIdeal R)) rs) :
    IsWeaklyRegular N rs ∧ Flat R (N ⧸ (Ideal.ofList rs • (⊤ : Submodule S N))) := by
  induction rs generalizing N with
  | nil =>
    refine ⟨by simp, ?_⟩
    exact Flat.of_linearEquiv ((Submodule.quotEquivOfEqBot (Ideal.ofList ([] : List S) •
      (⊤ : Submodule S N)) (by simp)).restrictScalars R)
  | cons x rs ih =>
    obtain ⟨hx, ht⟩ := (isWeaklyRegular_cons_iff _ _ _).mp hrs
    obtain ⟨hxN, hflat⟩ := regular_and_flat_quotSMulTop_of_fibre (R := R) x hx
    let : Flat R (QuotSMulTop x N) := hflat
    have ht' : IsWeaklyRegular ((QuotSMulTop x N) ⊗[R]
        (R ⧸ IsLocalRing.maximalIdeal R)) rs :=
      ((QuotSMulTop.relativeTensorEquiv (R := R) x).isWeaklyRegular_congr rs).mpr ht
    obtain ⟨htN, htflat⟩ := ih ht'
    refine ⟨(isWeaklyRegular_cons_iff _ _ _).mpr ⟨hxN, htN⟩, ?_⟩
    let : Flat R (QuotSMulTop x N ⧸
      (Ideal.ofList rs • (⊤ : Submodule S (QuotSMulTop x N)))) := htflat
    exact Flat.of_linearEquiv
      ((Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner N x rs).restrictScalars R)

/-- Every original prefix gives a base-flat quotient; no reordering or choice
of a replacement regular sequence is involved. -/
theorem flat_quotient_prefix_of_fibre_sequence (rs : List S)
    (hrs : IsWeaklyRegular (N ⊗[R] (R ⧸ IsLocalRing.maximalIdeal R)) rs) (n : ℕ) :
    Flat R (N ⧸ (Ideal.ofList (rs.take n) • (⊤ : Submodule S N))) := by
  have h : IsWeaklyRegular (N ⊗[R] (R ⧸ IsLocalRing.maximalIdeal R))
      (rs.take n ++ rs.drop n) := by simpa using hrs
  exact (regular_and_flat_quotient_of_fibre_sequence (R := R) (rs.take n)
    ((isWeaklyRegular_append_iff _ _ _).mp h).1).2

end Module.Flat

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFirstFractionAction

/-!
# Regular principal output centers on the actual first-successor atlas

The genuine action preserves the successive modification center. On each
constructed affine domain its generator is the regular input denominator;
flat restriction preserves both the full ideal and its regularity.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hn : 1 ≤ n)
  (f : WeierstrassDilatation.Coordinate W (π ^ (start + 0))
    (π * (data ⟨1, Nat.lt_succ_of_le hn⟩).b3)
    (π * (data ⟨1, Nat.lt_succ_of_le hn⟩).b4)
    (π ^ 2 * (data ⟨1, Nat.lt_succ_of_le hn⟩).b6))
  (hf : f ∈ WeierstrassSuccessiveX.modificationCenter W (π ^ (start + 0)) π
    (data ⟨1, Nat.lt_succ_of_le hn⟩).b3
    (data ⟨1, Nat.lt_succ_of_le hn⟩).b4
    (data ⟨1, Nat.lt_succ_of_le hn⟩).b6)
local notation "e" => data (Fin.mk 1 (Nat.lt_succ_of_le hn))
local notation "B" => WeierstrassDilatation.Coordinate W (π ^ (start + 0))
  (π * (Data.b3 e)) (π * (Data.b4 e)) (π ^ 2 * (Data.b6 e))
local notation "I" => WeierstrassSuccessiveX.modificationCenter W (π ^ (start + 0)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "C" => BlowupFractionChart.chart I f
local notation "c" => finiteSuccessiveFractionChart hπ data 0 hn f hf
local notation "v" => finiteNormalizedChart hπ data 0 hn

local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "q" => previousOriginalMap hπ d e
local notation "U" => firstFractionCover hπ data hn f hf


local notation "E" => initialExterior d

/-- The retained input denominator on an actual first-successor presentation. -/
def firstFractionDenominator (i : (U).I₀) : (U).X i :=
  firstFractionHom hπ data hn f hf i (BlowupFractionChart.denominator I f)

/-- The entire output center is the ideal of the actual retained input denominator. -/
theorem firstFractionAlpha_center (i : (U).I₀) :
    (I).map (firstFractionAlpha hπ data hn f hf i) =
      Ideal.span {firstFractionDenominator hπ data hn f hf i} := by
  exact WeierstrassSuccessiveX.successiveFractionAction_principal (S := (U).X i)
    W (π ^ (start + 0)) π (e).b3 (e).b4 (e).b6
    (by rw [← factor3_step hπ d e]; exact (d).factor3)
    (by rw [← factor4_step hπ d e]; exact (d).factor4)
    (by rw [← factor6_step hπ d e]; exact (d).factor6)
    (firstFractionParameter hπ data hn f hf i)
    (firstFractionAlphaAlg hπ data hn f hf i) (firstFractionBetaAlg hπ data hn f hf i)
    (firstFractionAlg_parameter hπ data hn f hf i)
    (firstFractionAlg_addition hπ data hn f hf i)
    (WeierstrassSuccessiveX.successiveFractionPresentation_scale_regular (S := (U).X i)
      W (π ^ (start + 0)) π (e).b3 (e).b4 (e).b6 f
      (firstFractionBetaAlg hπ data hn f hf i) (firstFractionHom hπ data hn f hf i)
      (firstFractionBetaAlg_factor hπ data hn f hf i)
      (firstFractionHom_flat hπ data hn f hf i)
      (IsRegular.of_ne_zero (pow_ne_zero _ hπ)))
    f hf (firstFractionHom hπ data hn f hf i)
    (firstFractionBetaAlg_factor hπ data hn f hf i)

/-- Its generator remains regular even on exceptional-fiber presentations. -/
theorem firstFractionDenominator_regular (i : (U).I₀) :
    IsRegular (firstFractionDenominator hπ data hn f hf i) :=
  flatRingHom_isRegular _ (firstFractionHom_flat hπ data hn f hf i)
    (BlowupFractionChart.denominator_regular I f)

/-- Arbitrary affine restrictions retain the exact full output center. -/
theorem firstFractionAlpha_mapped_center (i : (U).I₀) {S : Type u} [CommRing S]
    (ψ : (U).X i →+* S) :
    (I).map (ψ.comp (firstFractionAlpha hπ data hn f hf i)) =
      Ideal.span {ψ (firstFractionDenominator hπ data hn f hf i)} :=
  RegularCenter.mapped_center I _ _ (firstFractionAlpha_center hπ data hn f hf i) ψ

/-- Flat affine restrictions retain regularity of the same output generator. -/
theorem firstFractionDenominator_mapped_regular (i : (U).I₀) {S : Type u} [CommRing S]
    (ψ : (U).X i →+* S) (hψ : RingHom.Flat ψ) :
    IsRegular (ψ (firstFractionDenominator hπ data hn f hf i)) :=
  flatRingHom_isRegular ψ hψ (firstFractionDenominator_regular hπ data hn f hf i)

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFirstFractionOpen

/-!
# Full pullback comparison of first-successor fraction domains

The constructed fraction/divided domains coincide with the fraction
branches of the complete divided-output input cover. The comparison is
an isomorphism of entire schemes, retaining both input and output maps.
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

/-- The fraction product is the entire inverse image of its actual successor input chart. -/
theorem firstFractionInput_isPullback :
    IsPullback (pullback.snd (integralSmoothStructure W)
        (c ≫ finiteGlobalStructure hπ data 1 hn)) (firstFractionInput hπ data hn f hf)
      c (pullback.snd (integralSmoothStructure W) (finiteGlobalStructure hπ data 1 hn)) := by
  apply IsPullback.of_bot _ (by simp only [firstFractionInput, pullback.lift_snd])
    (IsPullback.of_hasPullback (integralSmoothStructure W)
      (finiteGlobalStructure hπ data 1 hn)).flip
  simpa only [firstFractionInput, pullback.lift_fst] using
    (IsPullback.of_hasPullback (integralSmoothStructure W)
      (c ≫ finiteGlobalStructure hπ data 1 hn)).flip

/-- Simultaneous divided outputs are the full pullback of the fraction product embedding. -/
theorem firstFractionToDividedOutput_product_isPullback :
    IsPullback (firstFractionToDividedOutput hπ data hn f hf)
      (pullback.fst (firstFractionOutput hπ data hn f hf) v)
      (pullback.fst (firstActionOutput hπ data hn) v)
      (firstFractionInput hπ data hn f hf) := by
  apply IsPullback.of_right _ (firstFractionToDividedOutput_fst hπ data hn f hf)
    (IsPullback.of_hasPullback (firstActionOutput hπ data hn) v).flip
  simpa only [firstFractionToDividedOutput_snd, firstFractionOutput] using
    (IsPullback.of_hasPullback (firstFractionOutput hπ data hn f hf) v).flip

/-- This is exactly the full fraction branch of the complete divided-output domain. -/
theorem firstFractionToDividedOutput_isPullback :
    IsPullback (firstFractionToDividedOutput hπ data hn f hf)
      (pullback.fst (firstFractionOutput hπ data hn f hf) v ≫ pullback.snd _ _)
      (firstDividedOutputInput hπ data hn) c :=
  (firstFractionToDividedOutput_product_isPullback hπ data hn f hf).paste_vert
    (firstFractionInput_isPullback hπ data hn f hf).flip

/-- The two independently constructed simultaneous fraction domains are canonically isomorphic. -/
def firstFractionDomainIso : firstFractionDomain hπ data hn f hf ≅
    pullback (firstDividedOutputInput hπ data hn) c :=
  (firstFractionToDividedOutput_isPullback hπ data hn f hf).isoPullback

/-- The comparison identifies the actual inclusion in the complete divided-output domain. -/
@[reassoc] theorem firstFractionDomainIso_hom_fst :
    (firstFractionDomainIso hπ data hn f hf).hom ≫ pullback.fst _ _ =
      firstFractionToDividedOutput hπ data hn f hf :=
  (firstFractionToDividedOutput_isPullback hπ data hn f hf).isoPullback_hom_fst

/-- Its inverse retains the same whole divided-output input. -/
@[reassoc] theorem firstFractionDomainIso_inv_fst :
    (firstFractionDomainIso hπ data hn f hf).inv ≫
      firstFractionToDividedOutput hπ data hn f hf = pullback.fst _ _ :=
  (firstFractionToDividedOutput_isPullback hπ data hn f hf).isoPullback_inv_fst

end FLT.Mazur.WeierstrassDividedDepth

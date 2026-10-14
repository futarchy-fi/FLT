/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveSplitOriginalSmooth
public import FLT.Mazur.WeierstrassDividedGlobalFiniteSmoothEmbedding
public import FLT.Mazur.WeierstrassDividedPositiveEqualitySmoothSpecialization

/-!
# The identity component retains the integral family's original smooth embedding

The residue identity chart is compatible with the original integral smooth
open. Its actual projection to the family agrees on all points and functions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open WeierstrassIntegralChart

variable {R : Type u} [CommRing R]
variable [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hk : 2 * (start + s + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "f" => finiteGlobalStructure hπ data (s + 1) hs

/-- The original identity embedding retains the residue coefficient structure. -/
@[reassoc] theorem positiveSplitOriginalSmoothMap_structure :
    positiveSplitOriginalSmoothMap hπ data D s hs hk ≫ pullback.fst q f =
      integralSmoothStructure (W.map (algebraMap R K)) := by
  let hd := lt_of_lt_of_le (Nat.mul_pos (by decide) (Nat.succ_pos _)) hk
  apply (cancel_epi (infinityResidueSmoothIso D hd).hom).mp
  simp only [positiveSplitOriginalSmoothMap, Category.assoc, Iso.hom_inv_id_assoc]
  rw [infinityLaurentChart_structure, ← infinityResidueSmoothGroupIso_inv]
  exact (infinityResidueSmoothGroupIso D hd).inv.hom.hom.hom.w.symm

/-- The complete residue identity embedding is the specialization of the retained integral one. -/
@[reassoc] theorem positiveSplitOriginalSmoothMap_specialization :
    positiveSplitOriginalSmoothMap hπ data D s hs hk ≫ pullback.snd q f =
      originalSmoothCoefficientMap K W ≫ finiteGlobalSmoothEmbedding hπ data (s + 1) hs := by
  let H := finiteGlobalSmoothEmbedding_isPullback hπ data (s + 1) hs
  let g := positiveSplitOriginalSmoothMap hπ data D s hs hk ≫ pullback.snd q f
  have hw : originalSmoothCoefficientMap K W ≫ (integralSmoothOpen W).ι =
      g ≫ finiteGlobalContraction hπ data (s + 1) hs := by
    rw [originalSmoothCoefficientMap_inclusion]
    exact (Category.assoc _ _ _).trans
      (positiveSplitOriginalSmoothMap_contraction hπ data D s hs hk) |>.symm
  have hl : H.lift (originalSmoothCoefficientMap K W) g hw =
      originalSmoothCoefficientMap K W := by
    simpa only [Category.comp_id] using H.lift_fst (originalSmoothCoefficientMap K W) g hw
  have he := H.lift_snd (originalSmoothCoefficientMap K W) g hw
  rw [hl] at he
  exact he.symm

end FLT.Mazur.WeierstrassDividedDepth

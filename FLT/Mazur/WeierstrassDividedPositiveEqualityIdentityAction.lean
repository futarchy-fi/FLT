/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalCoefficientSmoothOrbit
public import FLT.Mazur.WeierstrassDividedPositiveEqualityCartesian

/-!
# The actual action on the residue identity component

The original residue smooth identity component is stable under the integral
model's specialized action, with exactly its intrinsic smooth group law.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hk : 2 * (start + s + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "V" => W.map (algebraMap R K)
local notation "emb" => positiveEqualityOriginalSmoothMap hπ data D s hs hk

/-- The actual specialized action on the full identity component is intrinsic addition. -/
theorem positiveEqualityOriginalSmoothMap_action {T : Scheme.{u}}
    (a b : T ⟶ (integralSmoothOpen V).toScheme)
    (h : a ≫ integralSmoothStructure V = b ≫ integralSmoothStructure V) :
    finiteGlobalCoefficientPointAction hπ data (s + 1) hs K a (b ≫ emb)
        (by rw [Category.assoc, positiveEqualityOriginalSmoothMap_structure]; exact h) =
      smoothPairPointAddition V a b h ≫ emb := by
  simpa only [positiveEqualityOriginalSmoothMap_eq_coefficientEmbedding] using
    finiteGlobalCoefficientPointAction_smoothEmbedding hπ data (s + 1) hs K a b h

/-- The Laurent chart of the residue identity component retains the extended smooth embedding. -/
@[reassoc] theorem positiveEqualityInfinityLaurentChart_smoothEmbedding :
    (infinityResidueSmoothIso D
      (lt_of_lt_of_le (Nat.mul_pos (by decide) (Nat.succ_pos _)) hk)).hom ≫
      finiteGlobalSmoothCoefficientEmbedding K hπ data (s + 1) hs =
      infinityLaurentChart hπ data D
        (lt_of_lt_of_le (Nat.mul_pos (by decide) (Nat.succ_pos _)) hk) (s + 1) hs := by
  rw [← positiveEqualityOriginalSmoothMap_eq_coefficientEmbedding hπ data D s hs hk]
  rw [positiveEqualityOriginalSmoothMap, Iso.hom_inv_id_assoc]

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSmoothCoefficientEmbedding
public import FLT.Mazur.WeierstrassDividedPositiveSplitSmoothSpecialization

/-!
# The original residue identity embedding is the integral coefficient pullback

The identified full residue identity chart is precisely the coefficient extension
of the retained integral smooth embedding, as an actual Cartesian scheme square.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open WeierstrassIntegralChart
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hk : 2 * (start + s + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "f" => finiteGlobalStructure hπ data (s + 1) hs

/-- The residue identity embedding is exactly the retained integral coefficient embedding. -/
theorem positiveSplitOriginalSmoothMap_eq_coefficientEmbedding :
    positiveSplitOriginalSmoothMap hπ data D s hs hk =
      finiteGlobalSmoothCoefficientEmbedding K hπ data (s + 1) hs := by
  apply pullback.hom_ext
  · rw [positiveSplitOriginalSmoothMap_structure,
      finiteGlobalSmoothCoefficientEmbedding_structure]
  · rw [positiveSplitOriginalSmoothMap_specialization,
      finiteGlobalSmoothCoefficientEmbedding_projection]

/-- The actual original residue identity chart is Cartesian over the integral smooth embedding. -/
theorem positiveSplitOriginalSmoothMap_isPullback :
    IsPullback (originalSmoothCoefficientMap K W)
      (positiveSplitOriginalSmoothMap hπ data D s hs hk)
      (finiteGlobalSmoothEmbedding hπ data (s + 1) hs) (pullback.snd q f) := by
  rw [positiveSplitOriginalSmoothMap_eq_coefficientEmbedding]
  exact finiteGlobalSmoothCoefficientEmbedding_isPullback K hπ data (s + 1) hs

/-- The full identity chart is precisely the inverse image of the retained integral smooth open. -/
theorem positiveSplitOriginalSmoothMap_range_specialization :
    Set.range (positiveSplitOriginalSmoothMap hπ data D s hs hk) =
      (pullback.snd q f) ⁻¹' Set.range (finiteGlobalSmoothEmbedding hπ data (s + 1) hs) := by
  rw [positiveSplitOriginalSmoothMap_eq_coefficientEmbedding]
  exact finiteGlobalSmoothCoefficientEmbedding_range K hπ data (s + 1) hs

/-- Its universal comparison retains every scheme-valued point, including finite subgroups. -/
def positiveSplitOriginalSmoothCartesianIso :
    (integralSmoothOpen (W.map (algebraMap R K))).toScheme ≅
      pullback (finiteGlobalSmoothEmbedding hπ data (s + 1) hs) (pullback.snd q f) :=
  (positiveSplitOriginalSmoothMap_isPullback hπ data D s hs hk).isoPullback

/-- First projection is the actual coefficient map on the full original smooth scheme. -/
@[reassoc] theorem positiveSplitOriginalSmoothCartesianIso_fst :
    (positiveSplitOriginalSmoothCartesianIso hπ data D s hs hk).hom ≫
        pullback.fst _ _ = originalSmoothCoefficientMap K W :=
  (positiveSplitOriginalSmoothMap_isPullback hπ data D s hs hk).isoPullback_hom_fst

/-- Second projection is the original residue identity embedding with its cyclic orientation. -/
@[reassoc] theorem positiveSplitOriginalSmoothCartesianIso_snd :
    (positiveSplitOriginalSmoothCartesianIso hπ data D s hs hk).hom ≫
        pullback.snd _ _ = positiveSplitOriginalSmoothMap hπ data D s hs hk :=
  (positiveSplitOriginalSmoothMap_isPullback hπ data D s hs hk).isoPullback_hom_snd

end FLT.Mazur.WeierstrassDividedDepth

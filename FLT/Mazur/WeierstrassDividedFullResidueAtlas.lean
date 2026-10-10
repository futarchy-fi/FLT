/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialResidueAtlas
public import FLT.Mazur.WeierstrassDividedTerminalZeroNodalChart
public import FLT.Mazur.WeierstrassDividedZeroResidueAtlas

/-!
# A finite residue atlas at every starting depth and stage

The zero-stage terminal chart is its entire nodal affine cubic. At later
stages the full signed first nodes, subsequent positive-depth nodes and
terminal parity charts are retained. No starting depth is excluded.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (hdepth : 0 < depth)
local notation "K" => ResidueField R

/-- The three original indices at stage zero have their complete normal forms. -/
def globalStageZeroResidueAtlasRefinement (hstart : start = 0) (i : Fin 3) :
    (globalTensorAtlasObject hπ data K 0 (Nat.zero_le n) i).OpenCover := by
  classical
  by_cases hzero : i = 0
  · exact Scheme.coverOfIsIso (𝟙 _)
  by_cases hone : i = 1
  · subst i
    exact Scheme.coverOfIsIso
      (terminalZeroNodalAtlasIso hπ data D hdepth 0 (Nat.zero_le n) (by omega)).hom
  have hi0 : i.val ≠ 0 := fun h => hzero (Fin.ext h)
  have hi1 : i.val ≠ 1 := fun h => hone (Fin.ext h)
  exact initialZeroSlopeCoverAt hπ data D hdepth hstart 0 (Nat.zero_le n) i (by omega)

instance globalStageZeroResidueAtlasRefinement_finite
    (hstart : start = 0) (i : Fin 3) :
    Finite (globalStageZeroResidueAtlasRefinement hπ data D hdepth hstart i).I₀ := by
  classical
  unfold globalStageZeroResidueAtlasRefinement
  split_ifs
  · exact inferInstanceAs (Finite PUnit)
  · subst i
    exact inferInstanceAs (Finite PUnit)
  · infer_instance

variable (s : ℕ) (hs : s ≤ n) (hk : 2 * (start + s) ≤ depth)

/-- The full simultaneous normalization includes both zero and positive starting depths. -/
def globalFullResidueAtlasRefinement (i : Fin (s + 3)) :
    (globalTensorAtlasObject hπ data K s hs i).OpenCover := by
  classical
  by_cases hstart : start = 0
  · by_cases hs0 : s = 0
    · subst s
      exact globalStageZeroResidueAtlasRefinement hπ data D hdepth hstart i
    · exact globalZeroResidueAtlasRefinement hπ data D s hs hstart (by omega) hk i
  · exact globalInitialResidueAtlasRefinement hπ data D s hs (by omega) hk i

instance globalFullResidueAtlasRefinement_finite (i : Fin (s + 3)) :
    Finite (globalFullResidueAtlasRefinement hπ data D hdepth s hs hk i).I₀ := by
  classical
  unfold globalFullResidueAtlasRefinement
  split_ifs
  · subst s
    infer_instance
  · infer_instance
  · infer_instance

/-- These finitely many actual normal forms cover the entire projective residue model. -/
def globalFullResidueOpenCover : (finiteGlobalTensorModel hπ data K s hs).OpenCover :=
  (globalTensorOpenCover hπ data K s hs).bind
    (globalFullResidueAtlasRefinement hπ data D hdepth s hs hk)

instance globalFullResidueOpenCover_finite :
    Finite (globalFullResidueOpenCover hπ data D hdepth s hs hk).I₀ := by
  change Finite ((i : Fin (s + 3)) ×
    (globalFullResidueAtlasRefinement hπ data D hdepth s hs hk i).I₀)
  infer_instance

/-- Every normalized member keeps its original indexed global map. -/
theorem globalFullResidueOpenCover_map (i : Fin (s + 3))
    (a : (globalFullResidueAtlasRefinement hπ data D hdepth s hs hk i).I₀) :
    (globalFullResidueOpenCover hπ data D hdepth s hs hk).f ⟨i, a⟩ =
      (globalFullResidueAtlasRefinement hπ data D hdepth s hs hk i).f a ≫
        globalTensorAtlasMap hπ data K s hs i := rfl

/-- Every point belongs to a full normalized chart, without discarding a conic branch. -/
theorem globalFullResidueOpenCover_covers (z : finiteGlobalTensorModel hπ data K s hs) :
    ∃ i x, (globalFullResidueOpenCover hπ data D hdepth s hs hk).f i x = z :=
  (globalFullResidueOpenCover hπ data D hdepth s hs hk).exists_eq z

end FLT.Mazur.WeierstrassDividedDepth

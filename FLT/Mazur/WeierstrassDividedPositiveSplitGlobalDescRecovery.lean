/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveSplitGlobalDesc
public import FLT.Mazur.WeierstrassDividedPositiveSplitAtlasDescRecovery
import all FLT.Mazur.WeierstrassDividedPositiveSplitGlobalDesc
import all FLT.Mazur.WeierstrassDividedGlobalTensorAtlas

/-!
# Global strict-cycle descent recovers the identity of the original fiber

The local recovery equations hold at every original atlas index. Consequently
the global map constructed from the actual cyclic components is the identity.
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
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "Z" => positiveSplitCycleComponent hπ data D s hs hstart hk hp
local notation "F" => fun i => Over.Hom.left (Z i)
local notation "w" => positiveSplitCycleComponent_scheme_endpoints hπ data D s hs hstart hk hp

/-- The actual complete component maps descend to the identity on the entire original model. -/
theorem positiveSplitCycleGlobalDesc_original :
    positiveSplitCycleGlobalDesc hπ data D s hs hstart hk hp F w =
      𝟙 (finiteGlobalTensorModel hπ data K (s + 1) hs) := by
  apply (globalTensorOpenCover hπ data K (s + 1) hs).hom_ext
  intro i
  change globalTensorAtlasMap hπ data K (s + 1) hs i ≫ _ =
    globalTensorAtlasMap hπ data K (s + 1) hs i ≫ _
  simpa only [Category.comp_id] using
    (positiveSplitCycleGlobalDesc_atlas hπ data D s hs hstart hk hp F w i).trans
      (positiveSplitCycleAtlasFamily_original hπ data D s hs hstart hk hp i)

end FLT.Mazur.WeierstrassDividedDepth

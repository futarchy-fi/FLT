/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroCycleAtlasTerminalReduction
public import FLT.Mazur.WeierstrassDividedZeroCycleTerminalAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedZeroCycleAtlasTerminalReduction
import all FLT.Mazur.WeierstrassDividedZeroCycleTerminalAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedZeroCycleAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedZeroCycleAtlasFamily

/-!
# Global descent of the actual compatible cyclic component family

All intersections of the original global finite atlas are now proved
compatible. Gluing constructs a map on the entire residue model and recovers
every original indexed local descent.
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
  (hstart : start = 0) (hp : 2 * (start + s + 1) < depth)
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 3) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "C" => ZeroSplitCycleAtlasCompatible hπ data D s hs hstart hp F w

local notation "K" => ResidueField R
local notation "U" => globalTensorOpenCover hπ data K (s + 1) hs
local notation "d" => zeroSplitCycleAtlasFamily hπ data D s hs hstart hp F w

/-- Every pair of original atlas charts has its full scheme overlap equality. -/
theorem zeroSplitCycleAtlasFamily_compatible : ∀ i k, C i k :=
  zeroSplitCycleAtlasCompatible_of_terminal_neighbor hπ data D s hs hstart hp F w
    (zeroSplitCycleAtlasCompatible_terminal_neighbor hπ data D hstart s hs hp F w)

/-- The cyclic family descends to the entire original global residue model. -/
def zeroSplitCycleGlobalDesc : finiteGlobalTensorModel hπ data K (s + 1) hs ⟶ Y :=
  (U).glueMorphisms d (zeroSplitCycleAtlasFamily_compatible hπ data D s hs hstart hp F w)

/-- The global descent recovers every complete original chart, including the terminal node. -/
@[reassoc] theorem zeroSplitCycleGlobalDesc_atlas (i : Fin (s + 1 + 3)) :
    globalTensorAtlasMap hπ data K (s + 1) hs i ≫
      zeroSplitCycleGlobalDesc hπ data D s hs hstart hp F w = d i :=
  (U).ι_glueMorphisms d (zeroSplitCycleAtlasFamily_compatible hπ data D s hs hstart hp F w) i

/-- The prescribed full chart restrictions determine the global descended morphism uniquely. -/
theorem zeroSplitCycleGlobalDesc_unique
    (f : finiteGlobalTensorModel hπ data K (s + 1) hs ⟶ Y)
    (h : ∀ i, globalTensorAtlasMap hπ data K (s + 1) hs i ≫ f = d i) :
    f = zeroSplitCycleGlobalDesc hπ data D s hs hstart hp F w := by
  apply (U).hom_ext
  intro i
  exact (h i).trans (zeroSplitCycleGlobalDesc_atlas hπ data D s hs hstart hp F w i).symm

end FLT.Mazur.WeierstrassDividedDepth

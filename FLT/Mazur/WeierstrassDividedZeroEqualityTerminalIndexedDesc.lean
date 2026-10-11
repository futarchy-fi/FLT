/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityTerminalCompatibility
import all FLT.Mazur.WeierstrassDividedZeroEqualityTerminalCompatibility

/-!
# Descent on the complete original terminal retained atlas chart

The two terminal attachment maps agree on the actual conic intersection.
The original two-node cover glues them without imposing a zero divided constant.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) = depth)
  (hpos : 0 < s)
local notation "K" => ResidueField R
local notation "U" => olderIndexedNodeOpenCover hπ data D s hs 0 (by omega) (by omega) hk
local notation "f" => olderIndexedNodeMap hπ data D s hs 0 (by omega) (by omega) hk
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 2) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "d₁" => zeroEqualityCycleTerminalFirstDesc data D s hs hk hp F w
local notation "d₂" => zeroEqualityCycleTerminalSecondDesc data D s hs hk hp F w hpos

/-- The original terminal cover carries both full-node maps from the same cyclic family. -/
def zeroEqualityCycleTerminalNodeFamily (i : Fin 2) : (U).X i ⟶ Y := by
  refine Fin.cases ?_ ?_ i
  · exact d₁
  · intro j
    exact d₂

/-- All four original terminal node intersections are compatible. -/
theorem zeroEqualityCycleTerminalNodeFamily_compatible (i j : Fin 2) :
    pullback.fst (f i) (f j) ≫ zeroEqualityCycleTerminalNodeFamily
      hπ data D s hs hk hp hpos F w i =
      pullback.snd (f i) (f j) ≫ zeroEqualityCycleTerminalNodeFamily
      hπ data D s hs hk hp hpos F w j := by
  fin_cases i <;> fin_cases j
  · congr 1
    exact (cancel_mono (f 0)).mp pullback.condition
  · exact zeroEqualityCycleTerminalDesc_indexed_compatible
      hπ data D s hs hk hp hpos F w _ _ Limits.pullback.condition
  · change pullback.fst (f 1) (f 0) ≫ d₂ = pullback.snd (f 1) (f 0) ≫ d₁
    rw [← cancel_epi (pullbackSymmetry (f 0) (f 1)).hom]
    simp only [← Category.assoc, pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd]
    exact (zeroEqualityCycleTerminalDesc_indexed_compatible
      hπ data D s hs hk hp hpos F w _ _ Limits.pullback.condition).symm
  · congr 1
    exact (cancel_mono (f 1)).mp pullback.condition

/-- Both full terminal attachments glue on the original fixed retained chart at index two. -/
def zeroEqualityCycleTerminalIndexedDesc :
    globalTensorAtlasObject hπ data K (s + 1) hs ⟨2, by omega⟩ ⟶ Y :=
  (U).glueMorphisms (zeroEqualityCycleTerminalNodeFamily
      hπ data D s hs hk hp hpos F w)
    (zeroEqualityCycleTerminalNodeFamily_compatible hπ data D s hs hk hp hpos F w)

/-- Descent recovers the full first attachment map on its original node open. -/
@[reassoc] theorem zeroEqualityCycleTerminalIndexedDesc_first :
    f 0 ≫ zeroEqualityCycleTerminalIndexedDesc
      hπ data D s hs hk hp hpos F w = d₁ := by
  change (U).f (0 : Fin 2) ≫ (U).glueMorphisms _ _ =
    zeroEqualityCycleTerminalNodeFamily hπ data D s hs hk hp hpos F w 0
  exact (U).ι_glueMorphisms _ _ (0 : Fin 2)

/-- The opposite restriction retains its original negative conic parameter. -/
@[reassoc] theorem zeroEqualityCycleTerminalIndexedDesc_second :
    f 1 ≫ zeroEqualityCycleTerminalIndexedDesc
      hπ data D s hs hk hp hpos F w = d₂ := by
  change (U).f (1 : Fin 2) ≫ (U).glueMorphisms _ _ =
    zeroEqualityCycleTerminalNodeFamily hπ data D s hs hk hp hpos F w 1
  exact (U).ι_glueMorphisms _ _ (1 : Fin 2)

end FLT.Mazur.WeierstrassDividedDepth

/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityTerminalCompatibility
import all FLT.Mazur.WeierstrassDividedPositiveEqualityTerminalCompatibility

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
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "U" => olderIndexedNodeOpenCover hπ data D s hs 0 (by omega) (by omega) hk
local notation "f" => olderIndexedNodeMap hπ data D s hs 0 (by omega) (by omega) hk
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 4) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "d₁" => positiveEqualityCycleTerminalFirstDesc data D s hs hk hp F w
local notation "d₂" => positiveEqualityCycleTerminalSecondDesc data D s hs hk hp F w

/-- The original terminal cover carries both full-node maps from the same cyclic family. -/
def positiveEqualityCycleTerminalNodeFamily (i : Fin 2) : (U).X i ⟶ Y := by
  refine Fin.cases ?_ ?_ i
  · exact d₁
  · intro j
    exact d₂

/-- All four original terminal node intersections are compatible. -/
theorem positiveEqualityCycleTerminalNodeFamily_compatible (i j : Fin 2) :
    pullback.fst (f i) (f j) ≫ positiveEqualityCycleTerminalNodeFamily
      hπ data D s hs hstart hk hp F w i =
      pullback.snd (f i) (f j) ≫ positiveEqualityCycleTerminalNodeFamily
      hπ data D s hs hstart hk hp F w j := by
  fin_cases i <;> fin_cases j
  · congr 1
    exact (cancel_mono (f 0)).mp pullback.condition
  · exact positiveEqualityCycleTerminalDesc_indexed_compatible
      hπ data D s hs hstart hk hp F w _ _ Limits.pullback.condition
  · change pullback.fst (f 1) (f 0) ≫ d₂ = pullback.snd (f 1) (f 0) ≫ d₁
    rw [← cancel_epi (pullbackSymmetry (f 0) (f 1)).hom]
    simp only [← Category.assoc, pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd]
    exact (positiveEqualityCycleTerminalDesc_indexed_compatible
      hπ data D s hs hstart hk hp F w _ _ Limits.pullback.condition).symm
  · congr 1
    exact (cancel_mono (f 1)).mp pullback.condition

/-- Both full terminal attachments glue on the original fixed retained chart at index two. -/
def positiveEqualityCycleTerminalIndexedDesc :
    globalTensorAtlasObject hπ data K (s + 1) hs ⟨2, by omega⟩ ⟶ Y :=
  (U).glueMorphisms (positiveEqualityCycleTerminalNodeFamily
      hπ data D s hs hstart hk hp F w)
    (positiveEqualityCycleTerminalNodeFamily_compatible hπ data D s hs hstart hk hp F w)

/-- Descent recovers the full first attachment map on its original node open. -/
@[reassoc] theorem positiveEqualityCycleTerminalIndexedDesc_first :
    f 0 ≫ positiveEqualityCycleTerminalIndexedDesc
      hπ data D s hs hstart hk hp F w = d₁ := by
  change (U).f (0 : Fin 2) ≫ (U).glueMorphisms _ _ =
    positiveEqualityCycleTerminalNodeFamily hπ data D s hs hstart hk hp F w 0
  exact (U).ι_glueMorphisms _ _ (0 : Fin 2)

/-- The opposite restriction retains its original negative conic parameter. -/
@[reassoc] theorem positiveEqualityCycleTerminalIndexedDesc_second :
    f 1 ≫ positiveEqualityCycleTerminalIndexedDesc
      hπ data D s hs hstart hk hp F w = d₂ := by
  change (U).f (1 : Fin 2) ≫ (U).glueMorphisms _ _ =
    positiveEqualityCycleTerminalNodeFamily hπ data D s hs hstart hk hp F w 1
  exact (U).ι_glueMorphisms _ _ (1 : Fin 2)

end FLT.Mazur.WeierstrassDividedDepth

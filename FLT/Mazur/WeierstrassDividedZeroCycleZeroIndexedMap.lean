/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import all FLT.Mazur.WeierstrassDividedZeroCycleAttachmentMaps

public import FLT.Mazur.WeierstrassDividedZeroCycleAttachmentCompatibility
import all FLT.Mazur.WeierstrassDividedZeroCycleAttachmentCompatibility
public import FLT.Mazur.WeierstrassDividedZeroCyclePositiveIndexedMap

/-!
# Descent on the complete original start-zero retained atlas chart

The two attachment maps from one cyclic family agree on their actual scheme
intersection, so the original two-node cover glues them without extra hypotheses.
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
  (hstart : start = 0) (hp : 2 * (start + s + 1) < depth)
local notation "K" => ResidueField R
local notation "U" => olderZeroIndexedNodeOpenCover hπ data D 0 (by omega) s (by omega)
  (by omega) (by omega)
local notation "f" => olderZeroIndexedNodeMap hπ data D 0 (by omega) s (by omega)
  (by omega) (by omega)
local notation "transport" => eqToHom (globalTensorAtlasObject_index_congr hπ data
  (a := 0 + 1 + s) (by omega) hs (by omega)
  (Fin.succ (Fin.mk (s + 1) (by omega))) (Fin.mk (s + 2) (by omega)) (by rfl))
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 3) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "d₁" => zeroSplitCycleFirstAttachmentDesc data D s hs hp F w
local notation "d₂" => zeroSplitCycleSecondAttachmentDesc data D s hs hp F w

/-- The original two-cover family retains the opposite signs of its node sources. -/
def zeroSplitCycleZeroNodeFamily (i : Fin 2) : (U).X i ⟶ Y := by
  refine Fin.cases ?_ ?_ i
  · exact d₁
  · intro j
    exact d₂

/-- All four intersections of the original retained start-zero node cover are compatible. -/
theorem zeroSplitCycleZeroNodeFamily_compatible (i j : Fin 2) :
    pullback.fst (f i) (f j) ≫ zeroSplitCycleZeroNodeFamily hπ data D s hs hstart hp F w i =
      pullback.snd (f i) (f j) ≫ zeroSplitCycleZeroNodeFamily hπ data D s hs hstart hp F w j := by
  fin_cases i <;> fin_cases j
  · congr 1
    exact (cancel_mono (f 0)).mp pullback.condition
  · exact zeroSplitCycleAttachmentDesc_indexed_compatible hπ data D s hs hstart hp F w
  · change pullback.fst (f 1) (f 0) ≫ d₂ = pullback.snd (f 1) (f 0) ≫ d₁
    rw [← cancel_epi (pullbackSymmetry (f 0) (f 1)).hom]
    simp only [← Category.assoc, pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd]
    exact (zeroSplitCycleAttachmentDesc_indexed_compatible hπ data D s hs hstart hp F w).symm
  · congr 1
    exact (cancel_mono (f 1)).mp pullback.condition

/-- The entire oldest retained chart receives the descended map at its fixed atlas index. -/
def zeroSplitCycleZeroIndexedDesc :
    globalTensorAtlasObject hπ data K (s + 1) hs ⟨s + 2, by omega⟩ ⟶ Y :=
  inv transport ≫ (U).glueMorphisms (zeroSplitCycleZeroNodeFamily hπ data D s hs hstart hp F w)
    (zeroSplitCycleZeroNodeFamily_compatible hπ data D s hs hstart hp F w)

/-- Descent recovers the full first attachment map on its original node open. -/
@[reassoc] theorem zeroSplitCycleZeroIndexedDesc_first :
    f 0 ≫ transport ≫ zeroSplitCycleZeroIndexedDesc hπ data D s hs hstart hp F w = d₁ := by
  simp only [zeroSplitCycleZeroIndexedDesc, IsIso.hom_inv_id_assoc]
  change (U).f (0 : Fin 2) ≫ (U).glueMorphisms _ _ =
    zeroSplitCycleZeroNodeFamily hπ data D s hs hstart hp F w 0
  exact (U).ι_glueMorphisms _ _ (0 : Fin 2)

/-- The opposite restriction retains its localized exterior translation. -/
@[reassoc] theorem zeroSplitCycleZeroIndexedDesc_second :
    f 1 ≫ transport ≫ zeroSplitCycleZeroIndexedDesc hπ data D s hs hstart hp F w = d₂ := by
  simp only [zeroSplitCycleZeroIndexedDesc, IsIso.hom_inv_id_assoc]
  change (U).f (1 : Fin 2) ≫ (U).glueMorphisms _ _ =
    zeroSplitCycleZeroNodeFamily hπ data D s hs hstart hp F w 1
  exact (U).ι_glueMorphisms _ _ (1 : Fin 2)

end FLT.Mazur.WeierstrassDividedDepth

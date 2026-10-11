/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import all FLT.Mazur.WeierstrassDividedPositiveEqualityInitialNodeDesc

public import FLT.Mazur.WeierstrassDividedPositiveEqualityInitialNodeCompatibility
import all FLT.Mazur.WeierstrassDividedPositiveEqualityInitialNodeCompatibility

/-!
# Descent on the entire original initial atlas chart

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
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "U" => initialIndexedNodeOpenCover hπ data D (s + 1) hs hstart (by omega)
local notation "f" => initialIndexedNodeMap hπ data D (s + 1) hs hstart (by omega)
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 4) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "d₁" => positiveEqualityInitialFirstNodeDesc data D s hk F w
local notation "d₂" => positiveEqualityInitialSecondNodeDesc data D s hk F w

/-- The original two-cover family retains the opposite signs of its node sources. -/
def positiveEqualityInitialNodeFamily (i : Fin 2) : (U).X i ⟶ Y := by
  refine Fin.cases ?_ ?_ i
  · exact d₁
  · intro j
    exact d₂

/-- All four intersections of the original initial node cover are compatible. -/
theorem positiveEqualityInitialNodeFamily_compatible (i j : Fin 2) :
    pullback.fst (f i) (f j) ≫ positiveEqualityInitialNodeFamily
      hπ data D s hs hstart hk F w i =
      pullback.snd (f i) (f j) ≫ positiveEqualityInitialNodeFamily
      hπ data D s hs hstart hk F w j := by
  fin_cases i <;> fin_cases j
  · congr 1
    exact (cancel_mono (f 0)).mp pullback.condition
  · exact positiveEqualityInitialNodeDesc_indexed_compatible
      hπ data D s hs hstart hk F w
  · change pullback.fst (f 1) (f 0) ≫ d₂ = pullback.snd (f 1) (f 0) ≫ d₁
    rw [← cancel_epi (pullbackSymmetry (f 0) (f 1)).hom]
    simp only [← Category.assoc, pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd]
    exact (positiveEqualityInitialNodeDesc_indexed_compatible
      hπ data D s hs hstart hk F w).symm
  · congr 1
    exact (cancel_mono (f 1)).mp pullback.condition

/-- The entire initial chart receives the descended map at its fixed atlas index. -/
def positiveEqualityInitialIndexedDesc :
    globalTensorAtlasObject hπ data K (s + 1) hs ⟨s + 3, by omega⟩ ⟶ Y :=
  (U).glueMorphisms (positiveEqualityInitialNodeFamily
      hπ data D s hs hstart hk F w)
    (positiveEqualityInitialNodeFamily_compatible hπ data D s hs hstart hk F w)

/-- Descent recovers the full first attachment map on its original node open. -/
@[reassoc] theorem positiveEqualityInitialIndexedDesc_first :
    f 0 ≫ positiveEqualityInitialIndexedDesc
      hπ data D s hs hstart hk F w = d₁ := by
  simp only [positiveEqualityInitialIndexedDesc]
  change (U).f (0 : Fin 2) ≫ (U).glueMorphisms _ _ =
    positiveEqualityInitialNodeFamily hπ data D s hs hstart hk F w 0
  exact (U).ι_glueMorphisms _ _ (0 : Fin 2)

/-- The opposite restriction retains its localized exterior translation. -/
@[reassoc] theorem positiveEqualityInitialIndexedDesc_second :
    f 1 ≫ positiveEqualityInitialIndexedDesc
      hπ data D s hs hstart hk F w = d₂ := by
  simp only [positiveEqualityInitialIndexedDesc]
  change (U).f (1 : Fin 2) ≫ (U).glueMorphisms _ _ =
    positiveEqualityInitialNodeFamily hπ data D s hs hstart hk F w 1
  exact (U).ι_glueMorphisms _ _ (1 : Fin 2)

end FLT.Mazur.WeierstrassDividedDepth

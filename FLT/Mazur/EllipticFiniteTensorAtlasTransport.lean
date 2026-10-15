/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFiniteTensorIndex
public import FLT.Mazur.WeierstrassDividedGlobalTensorAtlas
public import FLT.Mazur.WeierstrassDividedOlderGlobalTensorCharts
public import FLT.Mazur.WeierstrassDividedAdjacentRetainedTensor
public import FLT.Mazur.SchemeOpenChartRange

/-!
# Final-stage index transport preserves entire atlas images

The canonical identifications compose and preserve the original indexed
atlas maps, including their full underlying point sets.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra A S]
  {a b c : ℕ} (ha : a ≤ n) (hb : b ≤ n) (hc : c ≤ n)
  (hab : a = b) (hbc : b = c)

/-- Equal-stage identifications compose without changing the original model map. -/
@[reassoc] theorem finiteTensorIndexIso_comp :
    (finiteTensorIndexIso A hπ data S a b ha hb hab).hom ≫
      (finiteTensorIndexIso A hπ data S b c hb hc hbc).hom =
    (finiteTensorIndexIso A hπ data S a c ha hc (hab.trans hbc)).hom := by
  subst b
  subst c
  exact Category.id_comp _

/-- Equality transport agrees with the canonical index identification. -/
theorem finiteTensorIndexIso_eqToHom :
    (finiteTensorIndexIso A hπ data S a b ha hb hab).hom =
      eqToHom (finiteGlobalTensorModel_index_congr hπ data S ha hb hab) := by
  subst b
  rfl

/-- Transporting an indexed chart retains its entire original image. -/
theorem finiteTensorIndexIso_atlas_range (i : Fin (a + 3)) (k : Fin (b + 3))
    (hik : i.val = k.val) :
    Set.range (globalTensorAtlasMap hπ data S a ha i ≫
      (finiteTensorIndexIso A hπ data S a b ha hb hab).hom) =
    Set.range (globalTensorAtlasMap hπ data S b hb k) := by
  subst b
  have hik' : i = k := Fin.ext hik
  subst k
  rw [show (finiteTensorIndexIso A hπ data S a a ha hb rfl).hom = 𝟙 _ from rfl,
    Category.comp_id]

/-- The original divided chart retains its full image at an equal final stage. -/
theorem finiteTensorIndexIso_divided_range :
    Set.range (globalDividedTensorChart hπ data S a ha ≫
      (finiteTensorIndexIso A hπ data S a b ha hb hab).hom) =
    Set.range (globalDividedTensorChart hπ data S b hb) := by
  subst b
  rw [show (finiteTensorIndexIso A hπ data S a a ha hb rfl).hom = 𝟙 _ from rfl,
    Category.comp_id]

/-- The whole retained exterior has its original indexed image after final-stage transport. -/
theorem finiteTensorIndexIso_older_range (j r : ℕ) (hj : j + 1 ≤ n)
    (hr : j + 1 + r ≤ n) (he : j + 1 + r = b) (i : Fin (b + 3))
    (hi : r + 2 = i.val) :
    Set.range (olderGlobalTensorChart hπ data S j hj r hr ≫
      (finiteTensorIndexIso A hπ data S (j + 1 + r) b hr hb he).hom) =
    Set.range (globalTensorAtlasMap hπ data S b hb i) := by
  rw [← olderGlobalTensorChart_eq_index, Category.assoc,
    SchemeOpenChartRange.range_iso_comp]
  exact finiteTensorIndexIso_atlas_range A hπ data S hr hb he _ i hi

end FLT.Mazur.WeierstrassDividedDepth

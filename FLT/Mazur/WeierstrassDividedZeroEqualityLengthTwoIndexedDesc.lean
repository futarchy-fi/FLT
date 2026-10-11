/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

import all FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoLocalMaps

public import FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoCompatibility
import all FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoCompatibility
public import FLT.Mazur.WeierstrassDividedZeroCyclePositiveIndexedMap

/-!
# The complete original horizontal chart in the length-two equality cycle

Both the exterior and conic restrictions agree on the original node
intersection. Its full two-node cover therefore glues the length-two family.
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
  (D : SplitNodeDepth W π depth) (hs : 0 + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + 0 + 1) ≤ depth)
  (hp : 2 * (start + 0 + 1) = depth)
local notation "K" => ResidueField R
local notation "U" => olderZeroIndexedNodeOpenCover hπ data D 0 (by omega) 0 (by omega)
  (by omega) (by omega)
local notation "f" => olderZeroIndexedNodeMap hπ data D 0 (by omega) 0 (by omega)
  (by omega) (by omega)
local notation "transport" => eqToHom (globalTensorAtlasObject_index_congr hπ data
  (a := 0 + 1 + 0) (by omega) hs (by omega)
  (Fin.succ (Fin.mk (0 + 1) (by omega))) (Fin.mk (0 + 2) (by omega)) (by rfl))
variable {Y : Scheme.{u}}
  (F : Fin 2 → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "d₁" => zeroEqualityLengthTwoFirstDesc data D hs hk hp F w
local notation "d₂" => zeroEqualityLengthTwoSecondDesc data D hs hk hp F w

/-- The original two-cover family retains the opposite signs of its node sources. -/
def zeroEqualityLengthTwoNodeFamily (i : Fin 2) : (U).X i ⟶ Y := by
  refine Fin.cases ?_ ?_ i
  · exact d₁
  · intro j
    exact d₂

/-- All four intersections of the original retained start-zero node cover are compatible. -/
theorem zeroEqualityLengthTwoNodeFamily_compatible (i j : Fin 2) :
    pullback.fst (f i) (f j) ≫ zeroEqualityLengthTwoNodeFamily
      hπ data D hs hstart hk hp F w i =
      pullback.snd (f i) (f j) ≫ zeroEqualityLengthTwoNodeFamily
      hπ data D hs hstart hk hp F w j := by
  fin_cases i <;> fin_cases j
  · congr 1
    exact (cancel_mono (f 0)).mp pullback.condition
  · exact zeroEqualityLengthTwoDesc_indexed_compatible data D hs hk hp F w hπ hstart
  · change pullback.fst (f 1) (f 0) ≫ d₂ = pullback.snd (f 1) (f 0) ≫ d₁
    rw [← cancel_epi (pullbackSymmetry (f 0) (f 1)).hom]
    simp only [← Category.assoc, pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd]
    exact (zeroEqualityLengthTwoDesc_indexed_compatible data D hs hk hp F w hπ hstart).symm
  · congr 1
    exact (cancel_mono (f 1)).mp pullback.condition

/-- The entire oldest retained chart receives the descended map at its fixed atlas index. -/
def zeroEqualityLengthTwoIndexedDesc :
    globalTensorAtlasObject hπ data K (0 + 1) hs ⟨0 + 2, by omega⟩ ⟶ Y :=
  inv transport ≫ (U).glueMorphisms (zeroEqualityLengthTwoNodeFamily
      hπ data D hs hstart hk hp F w)
    (zeroEqualityLengthTwoNodeFamily_compatible hπ data D hs hstart hk hp F w)

/-- Descent recovers the full first attachment map on its original node open. -/
@[reassoc] theorem zeroEqualityLengthTwoIndexedDesc_first :
    f 0 ≫ transport ≫ zeroEqualityLengthTwoIndexedDesc
      hπ data D hs hstart hk hp F w = d₁ := by
  simp only [zeroEqualityLengthTwoIndexedDesc, IsIso.hom_inv_id_assoc]
  change (U).f (0 : Fin 2) ≫ (U).glueMorphisms _ _ =
    zeroEqualityLengthTwoNodeFamily hπ data D hs hstart hk hp F w 0
  exact (U).ι_glueMorphisms _ _ (0 : Fin 2)

/-- The opposite restriction retains its localized exterior translation. -/
@[reassoc] theorem zeroEqualityLengthTwoIndexedDesc_second :
    f 1 ≫ transport ≫ zeroEqualityLengthTwoIndexedDesc
      hπ data D hs hstart hk hp F w = d₂ := by
  simp only [zeroEqualityLengthTwoIndexedDesc, IsIso.hom_inv_id_assoc]
  change (U).f (1 : Fin 2) ≫ (U).glueMorphisms _ _ =
    zeroEqualityLengthTwoNodeFamily hπ data D hs hstart hk hp F w 1
  exact (U).ι_glueMorphisms _ _ (1 : Fin 2)

end FLT.Mazur.WeierstrassDividedDepth

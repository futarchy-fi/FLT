/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoIndexedDesc
public import FLT.Mazur.WeierstrassDividedZeroCycleAtlasSlopeIntersection
public import FLT.Mazur.WeierstrassDividedZeroEqualityExteriorMaps
import all FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoIndexedDesc
import all FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoLocalMaps
import all FLT.Mazur.WeierstrassDividedZeroEqualityExteriorMaps

/-!
# The full length-two horizontal and infinity overlap

The nonzero terminal constant is retained. Both maps restrict to the same
normalized exterior map on the entire punctured slope scheme.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (hs : 0 + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + 0 + 1) ≤ depth)
  (hp : 2 * (start + 0 + 1) = depth)
local notation "K" => ResidueField R
local notation "α" => residue R W.a₁
local notation "c" => residue R (Data.b6 (data (Fin.mk 1 (by omega))))
local notation "ha" => D.a₁_unit.map (residue R)
local notation "t" => Units.mk0 α (IsUnit.ne_zero ha)
local notation "i" => PrincipalOpenTransport.inclusion (slopePolynomial α)
local notation "q" => olderGlobalZeroSlopeToInfinity hπ data D 0 hs 0 hs hstart hk
local notation "f" => olderZeroIndexedNodeMap hπ data D 0 hs 0 hs hstart hk
local notation "m" => globalTensorAtlasMap hπ data K (0 + 1) hs
local notation "transport" => eqToHom (globalTensorAtlasObject_index_congr hπ data
  (a := 0 + 1 + 0) hs hs (by omega)
  (Fin.succ (Fin.mk (0 + 1) (by omega))) (Fin.mk (0 + 2) (by omega)) (by rfl))
variable {Y : Scheme.{u}}
  (F : Fin 2 → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ j, ProjectiveLine.zero (ResidueField R) ≫ F j =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) j))
local notation "d" => zeroEqualityLengthTwoIndexedDesc hπ data D hs hstart hk hp F w

omit [IsBezout R] in
/-- The entire slope boundary factors through the original first exterior branch. -/
theorem zeroEqualityLengthTwoSlopeToAtlas_first :
    zeroSplitCycleSlopeToZeroAtlas hπ data D 0 hs hstart hk =
      fullNodeSlopeFirstBranch α c ha ≫ fullNodeSecondBranch α c ha ≫ f 0 ≫ transport := by
  simp only [zeroSplitCycleSlopeToZeroAtlas, eqToIso.hom, olderZeroIndexedNodeMap,
    Fin.cases_zero, Category.assoc, fullNodeSecondBranch_firstChart_assoc,
    fullNodeSlopeFirstBranch_open_assoc, fiberExteriorSlopeChart_incidence_assoc]

omit [IsBezout R] in
/-- The full horizontal descent recovers the normalized exterior slope map. -/
@[reassoc] theorem zeroEqualityLengthTwoIndexedDesc_slope :
    zeroSplitCycleSlopeToZeroAtlas hπ data D 0 hs hstart hk ≫ d =
      i ≫ ProjectiveLine.left K ≫ (ProjectiveLine.slopeNormalizationIso t).hom ≫ F 0 := by
  rw [zeroEqualityLengthTwoSlopeToAtlas_first]
  simp only [Category.assoc, zeroEqualityLengthTwoIndexedDesc_first,
    zeroEqualityLengthTwoFirstDesc_exterior, fullNodeSlopeFirstBranch_open_assoc]
  rfl

/-- The whole infinity chart has the same full punctured slope restriction. -/
@[reassoc] theorem zeroEqualityLengthTwoInfinityDesc_slope :
    q ≫ zeroEqualityCycleInfinityDesc hπ data D 0 hs hstart hk F =
      i ≫ ProjectiveLine.left K ≫ (ProjectiveLine.slopeNormalizationIso t).hom ≫ F 0 := by
  let ι := zeroRetainedExteriorInfinityChart hπ data D 0 hs 0 hs hstart hk
  let l := zeroRetainedExteriorAffineChart hπ data D 0 hs 0 hs hstart hk
  have H : q ≫ ι = i ≫ l :=
    (zeroRetainedExteriorCharts_isPullback hπ data D 0 hs 0 hs hstart hk).w.symm
  simp only [zeroEqualityCycleInfinityDesc, ← Category.assoc]
  rw [H]
  simp only [l, Category.assoc, zeroRetainedExteriorOrientedIso_affine_assoc]

/-- Infinity and the entire horizontal chart agree on their actual categorical intersection. -/
theorem zeroEqualityLengthTwoIndexedDesc_infinity_compatible :
    pullback.fst (m 0) (m ⟨2, by omega⟩) ≫
      zeroEqualityCycleInfinityDesc hπ data D 0 hs hstart hk F =
      pullback.snd (m 0) (m ⟨2, by omega⟩) ≫ d := by
  let H := zeroSplitCycleSlopeAtlas_isPullback hπ data D 0 hs hstart hk
  apply (cancel_epi H.isoPullback.hom).mp
  simp only [← Category.assoc, IsPullback.isoPullback_hom_fst,
    IsPullback.isoPullback_hom_snd]
  exact (zeroEqualityLengthTwoInfinityDesc_slope hπ data D hs hstart hk F).trans
    (zeroEqualityLengthTwoIndexedDesc_slope hπ data D hs hstart hk hp F w).symm

end FLT.Mazur.WeierstrassDividedDepth

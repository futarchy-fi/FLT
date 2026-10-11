/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityAtlasCompatibility
public import FLT.Mazur.WeierstrassDividedZeroCycleAtlasSlopeIntersection
import all FLT.Mazur.WeierstrassDividedZeroEqualityAtlasCompatibility
import all FLT.Mazur.WeierstrassDividedZeroCycleAtlasSlopeIntersection
import all FLT.Mazur.WeierstrassDividedZeroEqualityPositiveInitialDesc
import all FLT.Mazur.WeierstrassDividedZeroEqualityPositiveAttachmentMaps
import all FLT.Mazur.WeierstrassDividedZeroEqualityExteriorMaps
import all FLT.Mazur.WeierstrassDividedZeroEqualityPositiveAtlasFamily

/-!
# Equality-cycle compatibility of the initial attachment with infinity

Both descended maps have the same restriction on the full punctured slope
scheme. Its proved cartesian square gives equality on the original atlas overlap.
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
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth) (hpos : 0 < s)
local notation "K" => ResidueField R
local notation "α" => residue R W.a₁
local notation "c" => residue R (Data.b6 (data (Fin.mk 1 (by omega))))
local notation "ha" => D.a₁_unit.map (residue R)
local notation "t" => Units.mk0 α (IsUnit.ne_zero ha)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + 1) (by omega)
    (Data.b6 (data (Fin.mk 1 (by omega)))) (Data.factor6 (data (Fin.mk 1 (by omega)))))
local notation "i" => PrincipalOpenTransport.inclusion (slopePolynomial α)
local notation "q" => olderGlobalZeroSlopeToInfinity hπ data D 0 (by omega) s
  (by omega) (by omega) (by omega)
local notation "f" => olderZeroIndexedNodeMap hπ data D 0 (by omega) s (by omega)
  (by omega) (by omega)
local notation "transport" => eqToHom (globalTensorAtlasObject_index_congr hπ data
  (a := 0 + 1 + s) (by omega) hs (by omega)
  (Fin.succ (Fin.mk (s + 1) (by omega))) (Fin.mk (s + 2) (by omega)) (by rfl))
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 2) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ j, ProjectiveLine.zero (ResidueField R) ≫ F j =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) j))

omit [IsBezout R] in
/-- The glued oldest-chart map has exactly the original normalized slope restriction. -/
@[reassoc] theorem zeroEqualityPositiveCycleZeroIndexedDesc_slope :
    zeroSplitCycleSlopeToZeroAtlas hπ data D s hs hstart (by omega) ≫
        zeroEqualityPositiveCycleZeroIndexedDesc hπ data D s hs hstart hk hpos F w =
      i ≫ ProjectiveLine.left K ≫ (ProjectiveLine.slopeNormalizationIso t).hom ≫ F 0 := by
  have H : zeroSplitCycleSlopeToZeroAtlas hπ data D s hs hstart (by omega) =
      fullZeroNodeOverlapFirst α c ha hc ≫ f 0 ≫ transport := by
    simp only [zeroSplitCycleSlopeToZeroAtlas, eqToIso.hom, olderZeroIndexedNodeMap,
      Fin.cases_zero, Category.assoc, fullZeroNodeOverlapFirst_global_assoc]
  rw [H, Category.assoc, Category.assoc, zeroEqualityPositiveCycleZeroIndexedDesc_first,
    fullZeroNodeOverlapFirst_branch, Category.assoc,
    zeroEqualityPositiveCycleFirstAttachmentDesc_exterior, fullNodeSlopeFirstBranch_open_assoc]
  rfl

/-- The whole infinity map has the identical normalized slope restriction. -/
theorem zeroEqualityCycleInfinityDesc_slope :
    q ≫ zeroEqualityCycleInfinityDesc hπ data D s hs hstart (by omega) F =
      i ≫ ProjectiveLine.left K ≫ (ProjectiveLine.slopeNormalizationIso t).hom ≫ F 0 := by
  let ι := zeroRetainedExteriorInfinityChart hπ data D 0 (by omega) s
    (by omega) (by omega) (by omega)
  let l := zeroRetainedExteriorAffineChart hπ data D 0 (by omega) s
    (by omega) (by omega) (by omega)
  have H : q ≫ ι = i ≫ l :=
    (zeroRetainedExteriorCharts_isPullback hπ data D 0 (by omega) s
      (by omega) (by omega) (by omega)).w.symm
  simp only [zeroEqualityCycleInfinityDesc, ← Category.assoc]
  rw [H]
  simp only [l, Category.assoc, zeroRetainedExteriorOrientedIso_affine_assoc]

/-- The original oldest retained atlas chart and infinity satisfy scheme-morphism compatibility. -/
theorem zeroEqualityPositiveAtlasCompatible_zero_infinity :
    ZeroEqualityPositiveAtlasCompatible hπ data D s hs hstart hk hp hpos F w
      ⟨s + 2, by omega⟩ 0 := by
  apply zeroEqualityPositiveAtlasCompatible_symm hπ data D s hs hstart hk hp hpos F w
  unfold ZeroEqualityPositiveAtlasCompatible
  rw [zeroEqualityPositiveCycleAtlasFamily_infinity, zeroEqualityPositiveCycleAtlasFamily_zero]
  let H := zeroSplitCycleSlopeAtlas_isPullback hπ data D s hs hstart (by omega)
  apply (cancel_epi H.isoPullback.hom).mp
  simp only [← Category.assoc, IsPullback.isoPullback_hom_fst,
    IsPullback.isoPullback_hom_snd]
  exact (zeroEqualityCycleInfinityDesc_slope hπ data D s hs hstart hk hp hpos F).trans
    (zeroEqualityPositiveCycleZeroIndexedDesc_slope hπ data D s hs hstart hk hpos F w).symm

end FLT.Mazur.WeierstrassDividedDepth

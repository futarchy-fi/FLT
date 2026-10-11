/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityInitialNodeDesc
import all FLT.Mazur.WeierstrassDividedPositiveEqualityInitialNodeDesc
public import FLT.Mazur.WeierstrassModificationXZeroNodeOverlapBranches
public import FLT.Mazur.WeierstrassDividedInitialIndexedNodeCover

/-!
# The cyclic attachment descents agree on their entire original overlap

Both restrictions come from component zero with its same slope normalization.
Their equality is on the categorical pullback of the actual initial indexed
node maps, including the four-component cycle.
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
local notation "e" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 e)
local notation "ha" => D.a₁_unit.map (residue R)
local notation "t" => Units.mk0 a (IsUnit.ne_zero ha)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D start (by omega)
    (Data.b6 e) (Data.factor6 e))
local notation "f" => initialIndexedNodeMap hπ data D (s + 1) hs hstart (by omega)
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 4) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "d₁" => positiveEqualityInitialFirstNodeDesc data D s hk F w
local notation "d₂" => positiveEqualityInitialSecondNodeDesc data D s hk F w

/-- Both local cyclic descents agree on the full original normal-form intersection. -/
theorem positiveEqualityInitialNodeDesc_compatible :
    pullback.fst (fullFirstNodeChart a c ha) (fullSecondNodeChart a c ha) ≫ d₁ =
      pullback.snd (fullFirstNodeChart a c ha) (fullSecondNodeChart a c ha) ≫ d₂ := by
  apply fullZeroNodeMaps_compatible a c ha hc d₁ d₂
    (ProjectiveLine.left K ≫ (ProjectiveLine.slopeNormalizationIso t).hom ≫ F 0)
  · exact positiveEqualityInitialFirstNodeDesc_exterior data D s hk F w
  · exact positiveEqualityInitialSecondNodeDesc_exterior data D s hk F w

/-- The same equality holds on the actual initial indexed two-node cover intersection. -/
theorem positiveEqualityInitialNodeDesc_indexed_compatible :
    pullback.fst (f 0) (f 1) ≫ d₁ = pullback.snd (f 0) (f 1) ≫ d₂ := by
  let v := residueFiberIso D start hstart (by omega : 2 * start ≤ depth)
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) ≪≫
      finiteInitialTensorAtlasIso hπ data K (s + 1) hs
  have hf : f 0 = fullFirstNodeChart a c ha ≫ v.hom := by
    change (_ ≫ _) ≫ _ = _ ≫ (_ ≫ _)
    rw [Category.assoc]
  have hg : f 1 = fullSecondNodeChart a c ha ≫ v.hom := by
    change (_ ≫ _) ≫ _ = _ ≫ (_ ≫ _)
    rw [Category.assoc]
  have H : IsPullback (fullZeroNodeOverlapFirst a c ha hc)
      (fullZeroNodeOverlapSecond a c ha hc) (f 0) (f 1) := by
    rw [hf, hg]
    exact (fullZeroNodeOverlap_isPullback a c ha hc).of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) v
      (by simp) (by simp) (by simp) (by simp)
  apply (cancel_epi H.isoPullback.hom).mp
  simp only [← Category.assoc, IsPullback.isoPullback_hom_fst,
    IsPullback.isoPullback_hom_snd]
  have h := congrArg (fun q => (fullZeroNodeOverlapIso a c ha hc).hom ≫ q)
    (positiveEqualityInitialNodeDesc_compatible data D s hk F w)
  simpa only [← Category.assoc, fullZeroNodeOverlapFirst, fullZeroNodeOverlapSecond] using h

end FLT.Mazur.WeierstrassDividedDepth

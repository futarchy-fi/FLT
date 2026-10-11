/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoLocalMaps
public import FLT.Mazur.WeierstrassModificationXFullNodeOverlapCompatibility
public import FLT.Mazur.WeierstrassDividedOlderZeroIndexedNodeCover
import all FLT.Mazur.WeierstrassDividedZeroEqualityLengthTwoLocalMaps
import all FLT.Mazur.WeierstrassDividedEqualityTerminalNodeParameters

/-!
# Full length-two attachment compatibility at equality depth

Both entire conic parameters come from the same reversed terminal component,
and both exterior branches come from the same normalized exterior component.
Together they determine compatibility on the full original node intersection.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (hs : 0 + 1 ≤ n)
  (hk : 2 * (start + 0 + 1) ≤ depth) (hp : 2 * (start + 0 + 1) = depth)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (0 + 1) (Nat.lt_succ_of_le hs))
local notation "c" => residue R (Data.b6 e)
local notation "a" => residue R W.a₁
local notation "ha" => D.a₁_unit.map (residue R)
local notation "t" => Units.mk0 a (IsUnit.ne_zero ha)
local notation "hc" => IsUnit.map (residue R)
  (WeierstrassDilatation.divided_constant_isUnit D (start + 0 + 1)
    hp (Data.b6 e) (Data.factor6 e))
local notation "l" => laurentConicComponentConic D (start + 0) hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) (Data.factor6 e) hp
local notation "J" => laurentConicComponentProjectiveIso D (start + 0) hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) (Data.factor6 e) hp
variable {Y : Scheme.{u}}
  (F : Fin 2 → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by decide) i))
local notation "d₁" => zeroEqualityLengthTwoFirstDesc data D hs hk hp F w
local notation "d₂" => zeroEqualityLengthTwoSecondDesc data D hs hk hp F w

/-- The actual full local maps agree on both pieces of their original intersection. -/
theorem zeroEqualityLengthTwoDesc_compatible :
    pullback.fst (fullFirstNodeChart a c ha) (fullSecondNodeChart a c ha) ≫ d₁ =
      pullback.snd (fullFirstNodeChart a c ha) (fullSecondNodeChart a c ha) ≫ d₂ := by
  apply fullNodeMaps_compatible_of_component_restrictions a c ha hc d₁ d₂
    (ProjectiveLine.left K ≫ (ProjectiveLine.slopeNormalizationIso t).hom ≫ F 0)
    (l ≫ (J).inv ≫ ProjectiveLine.endpointReversal K ≫ F 1)
  · exact zeroEqualityLengthTwoFirstDesc_exterior data D hs hk hp F w
  · exact zeroEqualityLengthTwoSecondDesc_exterior data D hs hk hp F w
  · rw [zeroEqualityLengthTwoFirstDesc_conic]
    simp only [equalityTerminalFirstNodeParameter, laurentConicComponentFirstParameter,
      WeierstrassCurve.map_a₁, Category.assoc]
  · rw [zeroEqualityLengthTwoSecondDesc_conic]
    simp only [equalityTerminalSecondNodeParameter, laurentConicComponentSecondParameter,
      WeierstrassCurve.map_a₁, Category.assoc]

variable (hπ : π ≠ 0) (hstart : start = 0)
local notation "f" => olderZeroIndexedNodeMap hπ data D 0 hs 0 (by omega)
  (by omega) hk

/-- The full length-two descents also agree on the actual indexed retained-node overlap. -/
theorem zeroEqualityLengthTwoDesc_indexed_compatible :
    pullback.fst (f 0) (f 1) ≫ d₁ = pullback.snd (f 0) (f 1) ≫ d₂ := by
  let v := olderGlobalZeroAtlasIso hπ data D 0 hs 0 (by omega) (by omega) hk
  let b₁ := pullback.fst (f 0) (f 1)
  let b₂ := pullback.snd (f 0) (f 1)
  have he : b₁ ≫ fullFirstNodeChart a c ha = b₂ ≫ fullSecondNodeChart a c ha := by
    apply (cancel_mono v.hom).mp
    change pullback.fst (f 0) (f 1) ≫ f 0 = pullback.snd (f 0) (f 1) ≫ f 1
    exact pullback.condition
  have H := congrArg (fun q => pullback.lift b₁ b₂ he ≫ q)
    (zeroEqualityLengthTwoDesc_compatible data D hs hk hp F w)
  simpa only [← Category.assoc, pullback.lift_fst, pullback.lift_snd] using H

end FLT.Mazur.WeierstrassDividedDepth

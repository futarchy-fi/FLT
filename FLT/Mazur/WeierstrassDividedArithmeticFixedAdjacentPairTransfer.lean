/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticFixedAdjacentRange
public import FLT.Mazur.SchemePairSymmetryPoints

/-!
# Single boundary transfer on a fixed indexed arithmetic pair

Change only the first retained input on its full incidence open. The other
input is arbitrary, so this applies to mixed retained and terminal pairs.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
open scoped TensorProduct
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (m k : ℕ) (hk : k ≤ n) (j : ℕ) (hj : j + 2 ≤ k)
local notation "Q" => Quotient R π m
local notation "e" => data ⟨j + 1,
  Nat.lt_succ_of_le ((Nat.le_succ (j + 1)).trans (hj.trans hk))⟩
local notation "eNext" => data ⟨j + 2, by omega⟩
local notation "tt" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q 0
local notation "tu" => tensorCoord W (π ^ (start + (j + 1))) π
  (Data.b3 eNext) (Data.b4 eNext) (Data.b6 eNext) Q 2
local notation "ia" => (Fin.succ ⟨k - j,
  Nat.lt_succ_of_le ((Nat.sub_le k j).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "ib" => (Fin.succ ⟨k - (j + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (j + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk

local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "f" => chart ia ≫ s
local notation "f'" => chart ib ≫ s
local notation "src" => arithmeticFixedAdjacentBoundarySource hπ data m k hk j hj
local notation "tgt" => arithmeticFixedAdjacentBoundaryTarget hπ data m k hk j hj
local notation "H" => arithmeticFixedAdjacentBoundary_ambient hπ data m k hk j hj
local notation "I" => arithmeticFixedAdjacentSourceCoordinates hπ data m k hk j hj
local notation "J" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk j hj
attribute [local irreducible] arithmeticFixedAdjacentBoundarySource
  arithmeticFixedAdjacentBoundaryTarget arithmeticFixedAdjacentSourceCoordinates
  arithmeticFixedAdjacentTargetCoordinates
variable {Y : Scheme}
  (otherMap : Y ⟶ Spec (.of (PolygonArithmeticStages.Quotient R π m)))

/-- The full incidence domain inside the original indexed relative product. -/
def arithmeticFixedAdjacentPairOpen : (pullback f otherMap).Opens :=
  SchemePairBoundaryTransfer.domain f otherMap src

local notation "O" => arithmeticFixedAdjacentPairOpen hπ data m k hk j hj otherMap

/-- The domain uses the original retained incidence coordinate. -/
theorem arithmeticFixedAdjacentPairOpen_mem (p : (pullback f otherMap : Scheme)) :
    p ∈ O ↔ tt ∉ (I (pullback.fst f otherMap p)).asIdeal :=
  arithmeticFixedAdjacentBoundarySource_mem hπ data m k hk j hj _

/-- The actual single transfer, retaining the arbitrary second factor. -/
def arithmeticFixedAdjacentPairTransfer : (O).toScheme ⟶ pullback f' otherMap :=
  SchemePairBoundaryTransfer.transfer f f' otherMap src tgt (by
    simpa only [Category.assoc] using congrArg (fun z => z ≫ s) H)

local notation "T" => arithmeticFixedAdjacentPairTransfer hπ data m k hk j hj otherMap

/-- The first resolved input is preserved as a whole morphism. -/
@[reassoc] theorem arithmeticFixedAdjacentPairTransfer_first :
    T ≫ pullback.fst f' otherMap ≫ chart ib = (O).ι ≫ pullback.fst f otherMap ≫ chart ia :=
  SchemePairBoundaryTransfer.transfer_first_ambient f f' otherMap src tgt _ (chart ia) (chart ib) H

/-- The second input is preserved as a whole morphism. -/
@[reassoc] theorem arithmeticFixedAdjacentPairTransfer_second :
    T ≫ pullback.snd f' otherMap = (O).ι ≫ pullback.snd f otherMap :=
  SchemePairBoundaryTransfer.transfer_snd f f' otherMap src tgt _

/-- The transferred first input lies in the full original target boundary. -/
theorem arithmeticFixedAdjacentPairTransfer_range (p : (O).toScheme) :
    pullback.fst f' otherMap (T p) ∈ Set.range tgt := by
  exact SchemePairBoundaryTransfer.transfer_fst_mem_range f f' otherMap src tgt _ p

/-- The first target is punctured on the entire actual transfer domain. -/
theorem arithmeticFixedAdjacentPairTransfer_punctured (p : (O).toScheme) :
    tu ∉ (J (pullback.fst f' otherMap (T p))).asIdeal :=
  arithmeticFixedAdjacentBoundaryTarget_punctured hπ data m k hk j hj _
    (arithmeticFixedAdjacentPairTransfer_range hπ data m k hk j hj otherMap p)

end FLT.Mazur.WeierstrassDividedDepth

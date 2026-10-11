/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityPositiveAtlasFamily
public import FLT.Mazur.WeierstrassDividedZeroCyclePositiveTensorDesc
import all FLT.Mazur.WeierstrassDividedZeroEqualityPositiveAtlasFamily
import all FLT.Mazur.WeierstrassDividedZeroEqualityInteriorIndexedDesc
import all FLT.Mazur.WeierstrassDividedZeroCyclePositiveTensorDesc

/-!
# Entire interior retained tensor charts for the equality cycle

The numerical atlas isomorphism preserves both full node descents. Only the
strictly earlier constants vanish; the terminal chart is excluded here.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth) (hpos : 0 < s) (j : Fin (s - 1))
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j.val + 1 + 1) (by omega))
local notation "V" => zeroSplitCyclePositiveAtlasIso hπ data s hs (Fin.mk j.val (by omega))
local notation "N₁" => residueMiddleFirstNodeChart D (start + (j.val + 1)) (by omega)
  (by omega) (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "N₂" => residueMiddleSecondNodeChart D (start + (j.val + 1)) (by omega)
  (by omega) (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 2) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))

/-- Pull the actual equality family back to the complete earlier positive tensor chart. -/
def zeroEqualityCycleInteriorTensorDesc :=
  (V).hom ≫ zeroEqualityPositiveCycleAtlasFamily
    hπ data D s hs hstart hk hp hpos F w ⟨s - j.val + 1, by omega⟩

/-- The first full tensor node recovers the chosen earlier cyclic descent. -/
@[reassoc] theorem zeroEqualityCycleInteriorTensorDesc_first :
    N₁ ≫ zeroEqualityCycleInteriorTensorDesc hπ data D s hs hstart hk hp hpos j F w =
      zeroEqualityCycleInteriorFirstLocalDesc data D s hs hstart hk j F w := by
  rw [zeroEqualityCycleInteriorTensorDesc, zeroEqualityPositiveCycleAtlasFamily_positive]
  have H := zeroEqualityCycleInteriorIndexedDesc_first hπ data D s hs hstart hk j F w
  change (N₁ ≫ (olderSuccessiveTensorAtlasIso hπ data K (j.val + 1)
    (by omega) (s - (j.val + 1)) (by omega)).hom) ≫ _ ≫ _ = _ at H
  simpa only [zeroSplitCyclePositiveAtlasIso, Iso.trans_hom, asIso_hom,
    Category.assoc] using H

/-- The opposite full tensor node retains the original negative parameter map. -/
@[reassoc] theorem zeroEqualityCycleInteriorTensorDesc_second :
    N₂ ≫ zeroEqualityCycleInteriorTensorDesc hπ data D s hs hstart hk hp hpos j F w =
      zeroEqualityCycleInteriorSecondLocalDesc data D s hs hstart hk j F w := by
  rw [zeroEqualityCycleInteriorTensorDesc, zeroEqualityPositiveCycleAtlasFamily_positive]
  have H := zeroEqualityCycleInteriorIndexedDesc_second hπ data D s hs hstart hk j F w
  change (N₂ ≫ (olderSuccessiveTensorAtlasIso hπ data K (j.val + 1)
    (by omega) (s - (j.val + 1)) (by omega)).hom) ≫ _ ≫ _ = _ at H
  simpa only [zeroSplitCyclePositiveAtlasIso, Iso.trans_hom, asIso_hom,
    Category.assoc] using H

end FLT.Mazur.WeierstrassDividedDepth

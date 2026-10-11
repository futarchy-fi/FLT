/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityAtlasFamily
import all FLT.Mazur.WeierstrassDividedPositiveEqualityAtlasFamily
import all FLT.Mazur.WeierstrassDividedPositiveEqualityInteriorIndexedDesc

/-!
# Full earlier positive-start tensor charts carry the cyclic descents

Both complete node restrictions are retained after transporting the original
successive tensor chart into the fixed global atlas, including j = 0.
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
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth) (j : Fin s)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j.val + 1) (by omega))
local notation "V" => olderSuccessiveTensorAtlasIso hπ data K j.val
  (by omega) (s - j.val) (by omega)
local notation "T" => eqToHom (globalTensorAtlasObject_index_congr hπ data
  (a := j.val + 1 + (s - j.val)) (by omega) hs (by omega)
  (Fin.succ (Fin.mk (s - j.val + 1) (by omega)))
  (Fin.mk (s - j.val + 2) (by omega)) (by rfl))
local notation "N₁" => residueMiddleFirstNodeChart D (start + j.val) (by omega)
  (by omega) (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "N₂" => residueMiddleSecondNodeChart D (start + j.val) (by omega)
  (by omega) (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 4) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))

/-- The whole original tensor chart receives its map from the fixed atlas family. -/
def positiveEqualityCycleInteriorTensorDesc :
    Spec (.of (ScalarExtension W (π ^ (start + j.val)) π
      (Data.b3 e) (Data.b4 e) (Data.b6 e) K)) ⟶ Y :=
  (V).hom ≫ T ≫ positiveEqualityCycleAtlasFamily
    hπ data D s hs hstart hk hp F w ⟨s - j.val + 2, by omega⟩

/-- The first original full node restriction is unchanged by tensor transport. -/
@[reassoc] theorem positiveEqualityCycleInteriorTensorDesc_first :
    N₁ ≫ positiveEqualityCycleInteriorTensorDesc hπ data D s hs hstart hk hp j F w =
      positiveEqualityCycleInteriorFirstLocalDesc data D s hs hk j F w := by
  rw [positiveEqualityCycleInteriorTensorDesc, positiveEqualityCycleAtlasFamily_positive]
  have H := positiveEqualityCycleInteriorIndexedDesc_first hπ data D s hs hstart hk j F w
  change (N₁ ≫ (V).hom) ≫ T ≫ _ = _ at H
  simpa only [Category.assoc] using H

/-- The opposite full node restriction preserves its original negative parameter. -/
@[reassoc] theorem positiveEqualityCycleInteriorTensorDesc_second :
    N₂ ≫ positiveEqualityCycleInteriorTensorDesc hπ data D s hs hstart hk hp j F w =
      positiveEqualityCycleInteriorSecondLocalDesc data D s hs hk j F w := by
  rw [positiveEqualityCycleInteriorTensorDesc, positiveEqualityCycleAtlasFamily_positive]
  have H := positiveEqualityCycleInteriorIndexedDesc_second hπ data D s hs hstart hk j F w
  change (N₂ ≫ (V).hom) ≫ T ≫ _ = _ at H
  simpa only [Category.assoc] using H

end FLT.Mazur.WeierstrassDividedDepth

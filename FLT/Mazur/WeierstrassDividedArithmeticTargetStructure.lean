/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticFixedAdjacentPuncture

/-!
# Original coefficient structure on indexed arithmetic boundary targets

Undoing the retained index preserves the quotient coefficient map. Thus two
recovered targets have their common base over the actual arithmetic quotient.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  arithmeticRetainedTensorIso olderSuccessiveTensorAtlasIso finiteTensorAtlasObject
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (m k : ℕ) (hk : k ≤ n)
local notation "Q" => Quotient R π m

/-- Reindexing a retained chart preserves its original quotient coefficient morphism. -/
@[reassoc] theorem arithmeticRetainedTensorChart_structure (a : ℕ) (ha : a < k) :
    arithmeticRetainedTensorChart hπ data m k hk a ha ≫
      finiteGlobalArithmeticStructure hπ data k hk m =
        Spec.map (CommRingCat.ofHom (algebraMap Q
          (ScalarExtension W (π ^ (start + a)) π
            (Data.b3 (data ⟨a + 1, by omega⟩)) (Data.b4 (data ⟨a + 1, by omega⟩))
            (Data.b6 (data ⟨a + 1, by omega⟩)) Q))) := by
  obtain ⟨r, he⟩ := Nat.exists_eq_add_of_le (show a + 1 ≤ k by omega)
  subst k
  rw [arithmeticRetainedTensorChart_eq hπ data m (a + 1 + r) hk a ha r hk]
  exact finiteArithmeticOlderTensorChart_structure hπ data m a (by omega) r hk

variable (j : ℕ) (hj : j + 2 ≤ k)
local notation "e" => data ⟨j + 2, by omega⟩
local notation "T" => ScalarExtension W (π ^ (start + (j + 1))) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q
local notation "ib" => (Fin.succ ⟨k - (j + 1), by omega⟩ : Fin (k + 3))
local notation "coords" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk j hj

/-- The recovered target coordinates are an isomorphism of the full original chart. -/
instance arithmeticFixedAdjacentTargetCoordinates_isIso : IsIso coords := by
  unfold arithmeticFixedAdjacentTargetCoordinates
  infer_instance

/-- The target coordinate isomorphism retains the actual quotient coefficient structure. -/
@[reassoc] theorem arithmeticFixedAdjacentTargetCoordinates_structure :
    coords ≫ Spec.map (CommRingCat.ofHom (algebraMap Q T)) =
      arithmeticTensorAtlasMap hπ data m k hk ib ≫
        finiteGlobalArithmeticStructure hπ data k hk m := by
  have h := arithmeticRetainedTensorChart_structure hπ data m k hk (j + 1) (by omega)
  unfold arithmeticRetainedTensorChart at h
  unfold arithmeticFixedAdjacentTargetCoordinates
  rw [← h, Category.assoc, Iso.inv_hom_id_assoc]

end FLT.Mazur.WeierstrassDividedDepth

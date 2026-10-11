/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityInteriorTensorDesc
import all FLT.Mazur.WeierstrassDividedTensorAtlasComparison
import all FLT.Mazur.WeierstrassDividedGlobalTensorAtlas

/-!
# The complete positive retained tensor chart at its fixed cyclic atlas index

Only numerical stage and index transports enter this isomorphism. Its
original global tensor map is preserved, including the first retained pair.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (j : Fin s)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j.val + 1) (by omega))
local notation "transport" => eqToHom (globalTensorAtlasObject_index_congr hπ data
  (a := j.val + 1 + (s - j.val)) (by omega) hs (by omega)
  (Fin.succ (Fin.mk (s - j.val + 1) (by omega)))
  (Fin.mk (s - j.val + 2) (by omega)) (by rfl))
local notation "targetTransport" => eqToHom (finiteGlobalTensorModel_index_congr hπ data K
  (by omega : j.val + 1 + (s - j.val) ≤ n) hs (by omega))
local notation "G" => globalTensorAtlasMap hπ data K (s + 1) hs
  (Fin.mk (s - j.val + 2) (by omega))

local notation "V" => olderSuccessiveTensorAtlasIso hπ data K j.val (by omega)
  (s - j.val) (by omega)
/-- The entire original tensor chart at the fixed positive cyclic atlas index. -/
def positiveEqualityInteriorAtlasIso :
    Spec (.of (ScalarExtension W (π ^ (start + j.val)) π
      (Data.b3 e) (Data.b4 e) (Data.b6 e) K)) ≅
        globalTensorAtlasObject hπ data K (s + 1) hs ⟨s - j.val + 2, by omega⟩ :=
  (V).trans (asIso transport)

/-- The complete chart isomorphism preserves the original global tensor map. -/
@[reassoc] theorem positiveEqualityInteriorAtlasIso_global :
    (positiveEqualityInteriorAtlasIso hπ data s hs j).hom ≫ G =
      olderGlobalTensorChart hπ data K j.val (by omega)
        (s - j.val) (by omega) ≫ targetTransport := by
  simp only [positiveEqualityInteriorAtlasIso, Iso.trans_hom, asIso_hom, Category.assoc]
  rw [globalTensorAtlasMap_index_transport hπ data
    (a := j.val + 1 + (s - j.val)) (by omega) hs (by omega)
    (Fin.succ (Fin.mk (s - j.val + 1) (by omega)))
    (Fin.mk (s - j.val + 2) (by omega)) (by rfl),
    ← Category.assoc, olderGlobalTensorChart_eq_index]

end FLT.Mazur.WeierstrassDividedDepth

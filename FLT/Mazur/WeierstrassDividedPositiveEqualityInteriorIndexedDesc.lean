/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderZeroConstantNodeDescent
public import FLT.Mazur.WeierstrassDividedPositiveEqualityInteriorLocalMaps
import all FLT.Mazur.WeierstrassDividedPositiveEqualityInteriorLocalMaps
public import FLT.Mazur.WeierstrassDividedZeroCyclePositiveIndexedMap

/-!
# Equality-cycle descent on every strictly earlier positive-start retained atlas object

The two original node maps glue using their proved empty intersection, including j = 0. An
explicit index transport gives a map on the actual fixed finite atlas object.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))

variable (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth) (j : Fin s)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j.val + 1) (by omega))
local notation "c" => residue R (Data.b6 e)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + j.val + 1) (by omega)
    (Data.b6 e) (Data.factor6 e))
local notation "U" => olderIndexedNodeOpenCover hπ data D j.val (by omega)
  (s - j.val) (by omega) (by omega) (by omega)
local notation "transport" => eqToHom (globalTensorAtlasObject_index_congr hπ data
  (a := j.val + 1 + (s - j.val)) (by omega) hs (by omega)
  (Fin.succ (Fin.mk (s - j.val + 1) (by omega)))
  (Fin.mk (s - j.val + 2) (by omega)) (by rfl))
variable {Y : Scheme.{u}}
  (F : Fin (2 * s + 4) → (ProjectiveLine.scheme (ResidueField R) ⟶ Y))
  (w : ∀ i, ProjectiveLine.zero (ResidueField R) ≫ F i =
    ProjectiveLine.infinity (ResidueField R) ≫ F (PolygonPinching.next (by omega) i))
local notation "a" => positiveEqualityCycleInteriorFirstLocalDesc data D s hs hk j F w
local notation "b" => positiveEqualityCycleInteriorSecondLocalDesc data D s hs hk j F w
local notation "d" => olderZeroConstantIndexedDesc hπ data D j.val (by omega)
  (s - j.val) (by omega) (by omega) (by omega) a b hc

/-- The map on the entire original positive-depth retained chart, with the fixed atlas index. -/
def positiveEqualityCycleInteriorIndexedDesc :
    globalTensorAtlasObject hπ data K (s + 1) hs ⟨s - j.val + 2, by omega⟩ ⟶ Y :=
  inv transport ≫ d

/-- Pulling back to the first original node gives exactly its chosen cyclic descent. -/
@[reassoc] theorem positiveEqualityCycleInteriorIndexedDesc_first :
    (U).f (0 : Fin 2) ≫ transport ≫
        positiveEqualityCycleInteriorIndexedDesc hπ data D s hs hstart hk j F w =
      a := by
  simp only [positiveEqualityCycleInteriorIndexedDesc, IsIso.hom_inv_id_assoc]
  exact olderZeroConstantIndexedDesc_first hπ data D j.val (by omega)
    (s - j.val) (by omega) (by omega) (by omega) a b hc

/-- Pulling back to the opposite node preserves its original negative conic parameter. -/
@[reassoc] theorem positiveEqualityCycleInteriorIndexedDesc_second :
    (U).f (1 : Fin 2) ≫ transport ≫
        positiveEqualityCycleInteriorIndexedDesc hπ data D s hs hstart hk j F w =
      b := by
  simp only [positiveEqualityCycleInteriorIndexedDesc, IsIso.hom_inv_id_assoc]
  exact olderZeroConstantIndexedDesc_second hπ data D j.val (by omega)
    (s - j.val) (by omega) (by omega) (by omega) a b hc

end FLT.Mazur.WeierstrassDividedDepth

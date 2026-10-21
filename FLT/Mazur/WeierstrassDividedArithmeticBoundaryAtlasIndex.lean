/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticNewestIndex
public import FLT.Mazur.WeierstrassDividedArithmeticAdjacentIntersection

/-!
# Exact atlas indices of the original arithmetic boundary charts

The adjacent and terminal boundary constructions use the original indexed
arithmetic charts, with their entire scheme morphisms preserved.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (m j : ℕ) (hj : j + 1 ≤ n)
local notation "Q" => PolygonArithmeticStages.Quotient R π m

/-- Changing only a stage-number expression preserves the full arithmetic chart. -/
theorem arithmeticRetainedTensorChart_stage_heq (k l : ℕ) (hk : k ≤ n) (hl : l ≤ n)
    (hk' : j < k) (hl' : j < l) (h : k = l) :
    HEq (arithmeticRetainedTensorChart hπ data m k hk j hk')
      (arithmeticRetainedTensorChart hπ data m l hl j hl') := by
  subst l
  rfl

/-- Reorientation of coefficient pullbacks preserves equality with transported stage indices. -/
theorem arithmeticBoundaryReorientation_heq {X : Scheme} (k l : ℕ)
    (hk : k ≤ n) (hl : l ≤ n) (h : k = l)
    (u : X ⟶ finiteGlobalTensorModel hπ data Q k hk)
    (v : X ⟶ finiteGlobalTensorModel hπ data Q l hl) (huv : HEq u v) :
    HEq (u ≫ (pullbackSymmetry
      (Spec.map (CommRingCat.ofHom (algebraMap R Q)))
      (finiteGlobalStructure hπ data k hk)).hom)
      (v ≫ (pullbackSymmetry (Spec.map (CommRingCat.ofHom (algebraMap R Q)))
        (finiteGlobalStructure hπ data l hl)).hom) := by
  subst l
  cases eq_of_heq huv
  rfl

/-- The reassociated older boundary chart is the exact retained arithmetic atlas chart. -/
theorem arithmeticRetainedTensorChart_adjacent (r : ℕ) (hr : j + 2 + r ≤ n) :
    arithmeticRetainedTensorChart hπ data m (j + 2 + r) hr j (by omega) =
      finiteArithmeticAdjacentOldTensorChart hπ data m j hj r hr := by
  have hi := arithmeticRetainedTensorChart_eq hπ data m (j + 1) hj j (by omega)
    (r + 1) (by omega)
  have he := arithmeticBoundaryReorientation_heq hπ data m
    (j + 1 + (r + 1)) (j + 2 + r) (by omega) hr (by omega) _ _
    (adjacentRetainedOldGlobalTensorChart_heq hπ data Q j hj r hr)
  exact eq_of_heq ((arithmeticRetainedTensorChart_stage_heq hπ data m j
    (j + 2 + r) (j + 1 + (r + 1)) hr (by omega) (by omega) (by omega)
    (by omega)).trans ((heq_of_eq hi).trans he))

/-- The adjacent old chart uses precisely the full original indexed tensor source. -/
@[reassoc] theorem arithmeticBoundaryAtlas_adjacent (r : ℕ) (hr : j + 2 + r ≤ n) :
    (arithmeticRetainedTensorIso hπ data m (j + 2 + r) hr j (by omega)).hom ≫
      arithmeticTensorAtlasMap hπ data m (j + 2 + r) hr
        (Fin.succ ⟨j + 2 + r - j, by omega⟩) =
      finiteArithmeticAdjacentOldTensorChart hπ data m j hj r hr :=
  arithmeticRetainedTensorChart_adjacent hπ data m j hj r hr

/-- The terminal source uses the original index two, before the terminal index one. -/
@[reassoc] theorem arithmeticBoundaryAtlas_newest :
    (arithmeticRetainedTensorIso hπ data m (j + 1) hj j (by omega)).hom ≫
      arithmeticTensorAtlasMap hπ data m (j + 1) hj
        (Fin.succ ⟨j + 1 - j, by omega⟩) =
      finiteArithmeticNewestTensorChart hπ data m j hj :=
  arithmeticRetainedTensorChart_newest hπ data j hj m

end FLT.Mazur.WeierstrassDividedDepth

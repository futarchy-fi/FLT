/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootOrderedAdjacent
public import FLT.Mazur.WeierstrassDividedFinalAdjacentOverComponents

/-!
# Independent adjacent components at the original final indices

Assemble both scale cases at each retained level and transport only the stage
index. Every component and node keeps its original final label.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hk : 2 * (start + s + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "G" => coefficientShearGluedIso hπ data K 0 (s + 1) hs
local notation "p" => coefficientShearGluedStructure hπ data K 0 (s + 1) hs

/-- The independent adjacent pair at its actual final level and tangent index. -/
def coefficientShearRootFinalAdjacentComponent (j : Fin s) (i : Fin 2) :
    ProjectiveLine.scheme K ⟶ coefficientShearGlued hπ data K 0 (s + 1) hs :=
  let hj : j.val + 2 ≤ n := by omega
  let hm : j.val + 2 + (s - (j.val + 1)) ≤ n := by omega
  let d := data ⟨j.val + 2, Nat.lt_succ_of_le hj⟩
  let hc := divided_linear_mem D (start + (j.val + 1) + 1) (by omega)
    d.b3 d.b4 d.factor3 d.factor4
  let h3 := (residue_eq_zero_iff _).mpr hc.1
  let h4 := (residue_eq_zero_iff _).mpr hc.2
  coefficientShearRootOrderedAdjacent hπ data D j.val (by omega) hj
      (s - (j.val + 1)) hm h3 h4 i ≫
    (coefficientShearGluedIso hπ data K 0 (j.val + 2 + (s - (j.val + 1))) hm).hom ≫
    eqToHom (finiteGlobalTensorModel_index_congr hπ data K hm hs (by omega)) ≫ (G).inv

/-- Reconstruction preserves every original final adjacent component and its branch order. -/
@[reassoc] theorem coefficientShearRootFinalAdjacentComponent_original (j : Fin s) (i : Fin 2) :
    coefficientShearRootFinalAdjacentComponent hπ data D s hs hk j i ≫ (G).hom =
      finalAdjacentComponent hπ data D s hs hk j i := by
  simp only [coefficientShearRootFinalAdjacentComponent, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, coefficientShearRootOrderedAdjacent_original
    hπ data D j.val (by omega) (by omega) (by omega) (by omega)]
  rfl

/-- Both independent adjacent components preserve the residue-field structure. -/
@[reassoc] theorem coefficientShearRootFinalAdjacentComponent_structure (j : Fin s) (i : Fin 2) :
    coefficientShearRootFinalAdjacentComponent hπ data D s hs hk j i ≫ p =
      ProjectiveLine.toBase K := by
  rw [coefficientShearGluedStructure,
    coefficientShearRootFinalAdjacentComponent_original_assoc, finalAdjacentComponent_structure]

variable (hp : 2 * (start + s + 1) < depth)

/-- The preceding original retained-node index survives the complete comparison. -/
@[reassoc] theorem coefficientShearRootFinalAdjacentComponent_zero_original
    (j : Fin s) (i : Fin 2) :
    ProjectiveLine.zero K ≫
        coefficientShearRootFinalAdjacentComponent hπ data D s hs hk j i ≫ (G).hom =
      finalNodeSection hπ data D s hs hk hp (.inl (.inr (⟨j.val, by omega⟩, i))) := by
  rw [coefficientShearRootFinalAdjacentComponent_original, finalAdjacentComponent_zero]

/-- The following original retained-node index survives without a level shift. -/
@[reassoc] theorem coefficientShearRootFinalAdjacentComponent_infinity_original
    (j : Fin s) (i : Fin 2) :
    ProjectiveLine.infinity K ≫
        coefficientShearRootFinalAdjacentComponent hπ data D s hs hk j i ≫ (G).hom =
      finalNodeSection hπ data D s hs hk hp (.inl (.inr (⟨j.val + 1, by omega⟩, i))) := by
  rw [coefficientShearRootFinalAdjacentComponent_original, finalAdjacentComponent_infinity]

/-- The independent adjacent maps as actual morphisms over the residue field. -/
def coefficientShearRootFinalAdjacentOverComponent (j : Fin s) (i : Fin 2) :
    PolygonPinching.component K ⟶ Over.mk p :=
  Over.homMk (coefficientShearRootFinalAdjacentComponent hπ data D s hs hk j i)
    (coefficientShearRootFinalAdjacentComponent_structure hπ data D s hs hk j i)

end FLT.Mazur.WeierstrassDividedDepth

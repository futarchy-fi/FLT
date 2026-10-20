/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialAtlasIndex
public import FLT.Mazur.WeierstrassDividedGlobalSmoothAtlas
public import FLT.Mazur.WeierstrassDilatationUnitComparison

/-!
# Divided coordinates on the full retained initial chart at start zero

The scale at depth zero is one. Its explicit inverse coordinate map sends
the entire initial ModificationX chart to the depth-zero divided chart.
Retention preserves this map and the original cubic and base contractions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R : Type*} [CommRing R] {W : WeierstrassCurve R} {π : R}
  (d : Data W π 0)
local notation "unit" => (⟨π ^ 0, 1, by simp, by simp⟩ : Rˣ)
local notation "A" => WeierstrassDilatation.Coordinate W (π ^ 0) d.b3 d.b4 d.b6
local notation "B" => WeierstrassModificationX.Coordinate W (π ^ 0) d.b3 d.b4 d.b6

/-- At scale one, the original affine coordinates recover divided coordinates everywhere. -/
def initialFormulaCoordinateHom : A →ₐ[R] B :=
  (WeierstrassModificationX.fromOriginal W (π ^ 0) d.b3 d.b4 d.b6
    d.factor3 d.factor4 d.factor6).comp
    (WeierstrassDilatation.toOriginal W unit d.b3 d.b4 d.b6
      d.factor3 d.factor4 d.factor6)

/-- The new divided coordinates recover exactly the original affine coordinate map. -/
theorem initialFormulaCoordinateHom_original :
    (initialFormulaCoordinateHom d).comp
        (WeierstrassDilatation.fromOriginal W (π ^ 0) d.b3 d.b4 d.b6
          d.factor3 d.factor4 d.factor6) =
      WeierstrassModificationX.fromOriginal W (π ^ 0) d.b3 d.b4 d.b6
        d.factor3 d.factor4 d.factor6 := by
  unfold initialFormulaCoordinateHom
  rw [AlgHom.comp_assoc, WeierstrassDilatation.toOriginal_comp_fromOriginal,
    AlgHom.comp_id]

/-- Full integral initial coordinates, without restricting the contracted divided point. -/
def initialFormulaCoordinates : Spec (.of B) ⟶ chart d :=
  Spec.map (CommRingCat.ofHom (initialFormulaCoordinateHom d).toRingHom)

/-- These coordinates preserve the exact original cubic contraction. -/
@[reassoc] theorem initialFormulaCoordinates_cubic :
    initialFormulaCoordinates d ≫ toCurve d =
      WeierstrassModificationX.toCurve W (π ^ 0) d.b3 d.b4 d.b6
        d.factor3 d.factor4 d.factor6 := by
  change Spec.map _ ≫ (Spec.map _ ≫ _) = Spec.map _ ≫ _
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  exact congrArg (fun f => CommRingCat.ofHom f.toRingHom)
    (initialFormulaCoordinateHom_original d)

variable [IsDomain R] [IsBezout R] (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "d₀" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "idx" => (Fin.succ ⟨j + 1, Nat.lt_succ_self (j + 1)⟩ : Fin (j + 3))

/-- The entire original initial chart in its exact last global-atlas position. -/
def retainedInitialFormulaCoordinates :
    globalIntegralAtlasObject data j hj idx ⟶ chart d₀ :=
  eqToHom (finiteInitialExteriorObject_eq data j hj) ≫ initialFormulaCoordinates d₀

/-- Retention keeps all original cubic coordinates of the initial chart. -/
@[reassoc] theorem retainedInitialFormulaCoordinates_cubic :
    retainedInitialFormulaCoordinates data j hj ≫ toCurve d₀ =
      globalIntegralAtlasMap hπ data j hj idx ≫ finiteGlobalContraction hπ data j hj := by
  apply (cancel_epi (eqToHom (finiteInitialExteriorObject_eq data j hj).symm)).mp
  rw [retainedInitialFormulaCoordinates, ← Category.assoc, ← Category.assoc,
    eqToHom_trans, eqToHom_refl, Category.id_comp, initialFormulaCoordinates_cubic]
  change _ = eqToHom _ ≫ (finiteAtlasMap hπ data (initialExterior d₀) j hj _ ≫ _) ≫ _
  rw [Category.assoc, ← Category.assoc (eqToHom _), finiteInitialChart_eq_index,
    finiteLocalChart_contraction, finiteInitialChart_toCurve]

/-- The initial chart supplies the unchanged coefficient map required by pair formulas. -/
@[reassoc] theorem retainedInitialFormulaCoordinates_structure :
    retainedInitialFormulaCoordinates data j hj ≫
        Spec.map (CommRingCat.ofHom (algebraMap R
          (WeierstrassDilatation.Coordinate W (π ^ (0 + 0)) (d₀).b3 (d₀).b4 (d₀).b6))) =
      globalIntegralAtlasMap hπ data j hj idx ≫ finiteGlobalStructure hπ data j hj := by
  rw [← toCurve_structure d₀, ← Category.assoc, retainedInitialFormulaCoordinates_cubic hπ,
    Category.assoc]
  rw [finiteGlobalStructure]

end FLT.Mazur.WeierstrassDividedDepth

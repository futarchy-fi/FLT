/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDepthStructure
public import FLT.Mazur.WeierstrassDividedFiniteChartStructure

/-!
# Flatness of every actual finite local modification

The finite atlas retains the first x chart, all subsequent x charts, and
the final divided chart. Their maps to the original base are flat; descent
along this actual finite open cover proves flatness of the whole local model.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
open WeierstrassIntegralChart
local notation "E₀" => initialExterior (data (Fin.mk 0 (Nat.zero_lt_succ n)))

/-- Each exterior atlas chart retains a flat map to the original coefficient spectrum. -/
theorem finiteExteriorAtlas_structure_flat (j : ℕ) (hj : j ≤ n) (i : Fin (j + 1)) :
    Flat (finiteExteriorAtlasMap hπ data E₀ j hj i ≫
      (finiteExterior hπ data E₀ j hj).exteriorChart ≫
        finiteToCurve hπ data j hj ≫ integralCurveStructure W) := by
  induction j with
  | zero =>
    change Flat (𝟙 _ ≫ (E₀).exteriorChart ≫
      (𝟙 _ ≫ initialToCurve (data ⟨0, Nat.zero_lt_succ n⟩)) ≫ integralCurveStructure W)
    rw [Category.id_comp, Category.id_comp, initialToCurve_exterior_assoc,
      WeierstrassModificationX.toCurve_structure]
    let _ := WeierstrassModificationX.coordinate_flat_of_scale_ne_zero
      W (π ^ start) (data ⟨0, Nat.zero_lt_succ n⟩).b3
        (data ⟨0, Nat.zero_lt_succ n⟩).b4 (data ⟨0, Nat.zero_lt_succ n⟩).b6
        (pow_ne_zero start hπ)
    exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  | succ j ih =>
    cases i using Fin.cases with
    | zero =>
      rw [finiteExteriorAtlas_new_toCurve_assoc]
      exact stepX_structure_flat _ hπ _
    | succ i =>
      rw [finiteExteriorAtlas_old_toCurve_assoc]
      exact ih (Nat.le_of_succ_le hj) i

/-- The original structure map of the actual finite local model. -/
def finiteStructure (j : ℕ) (hj : j ≤ n) :
    finiteModification hπ data j hj ⟶ Spec (.of R) :=
  finiteToCurve hπ data j hj ≫ integralCurveStructure W

/-- Every finite local modification is flat over the original Bezout domain. -/
instance finiteStructure_flat (j : ℕ) (hj : j ≤ n) :
    Flat (finiteStructure hπ data j hj) := by
  apply IsZariskiLocalAtSource.of_openCover (P := @Flat)
    (finiteOpenCover hπ data E₀ j hj)
  intro i
  change Flat (finiteAtlasMap hπ data E₀ j hj i ≫ finiteStructure hπ data j hj)
  cases i using Fin.cases with
  | zero =>
    dsimp only [finiteAtlasMap, Fin.cases_zero, finiteStructure]
    rw [finiteDivided_toCurve_assoc]
    infer_instance
  | succ i =>
    dsimp only [finiteAtlasMap, Fin.cases_succ, finiteStructure]
    rw [Category.assoc]
    exact finiteExteriorAtlas_structure_flat hπ data j hj i

end FLT.Mazur.WeierstrassDividedDepth

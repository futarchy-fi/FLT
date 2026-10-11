/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteOriginalXOpen
public import FLT.Mazur.WeierstrassDividedOlderPointActionPropagation
public import FLT.Mazur.WeierstrassDividedChartRegularCenter
public import FLT.Mazur.WeierstrassSmoothSuccessiveIntegralCubicMaps

/-!
# Original cubic comparisons detect integral actions on older charts

The actual chart inclusion retains the product-scale cubic map. Regularity
of the output x therefore upgrades a cubic action square to an equality
in the original finite model, at any retained stage.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j + 1 ≤ n) (r : ℕ) (hr : j + 1 + r ≤ n)
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "A" => WeierstrassSuccessiveX.Coordinate W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "q" => successiveIntegralCubicMap e
local notation "c" => olderGlobalChart hπ data j hj r hr

/-- The actual retained global chart preserves the full original cubic map. -/
@[reassoc] theorem olderGlobalChart_cubic :
    c ≫ finiteGlobalContraction hπ data (j + 1 + r) hr =
      Spec.map (CommRingCat.ofHom (q).toRingHom) ≫ integralCurveChart W 2 := by
  rw [olderGlobalChart, Category.assoc, finiteLocalChart_contraction,
    olderSuccessiveChart_toCurve, xContraction_originalPresentation,
    successiveIntegralCubicMap_eq]
  rfl

variable {S : Type u} [CommRing S] [Algebra R S]
  (a : Spec (.of S) ⟶ (integralSmoothOpen W).toScheme)
  (f g : WeierstrassSuccessiveX.Coordinate W (π ^ (start + j)) π
    (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3
    (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4
    (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 →ₐ[R] S)
  (ha : a ≫ integralSmoothStructure W = Spec.map (CommRingCat.ofHom (algebraMap R S)))

include ha in
/-- Any original algebra input retains the coefficient compatibility of the smooth point. -/
theorem olderGlobalChart_algebra_condition :
    a ≫ integralSmoothStructure W =
      (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ c) ≫
        finiteGlobalStructure hπ data (j + 1 + r) hr := by
  rw [Category.assoc, olderGlobalChart_structure, specAlgHom_structure]
  exact ha

/-- A proved cubic action square with regular output x determines the actual finite action. -/
theorem olderGlobalChart_pointAction_of_cubic
    (hx : IsRegular ((g.comp q) (coord W 2 0)))
    (hadd : Spec.map (CommRingCat.ofHom (g.comp q).toRingHom) ≫ integralCurveChart W 2 =
      leftSmoothPointAddition W a
        (Spec.map (CommRingCat.ofHom (f.comp q).toRingHom) ≫ integralCurveChart W 2)
        (by simp only [Category.assoc, integralCurveChart_structure, chartStructure,
          specAlgHom_structure]; exact ha)) :
    finiteGlobalPointAction hπ data (j + 1 + r) hr a
      (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ c)
      (olderGlobalChart_algebra_condition hπ data j hj r hr a f ha) =
        Spec.map (CommRingCat.ofHom g.toRingHom) ≫ c := by
  apply finiteGlobalContraction_ext_of_regular_x hπ data (j + 1 + r) hr
    (g.comp q).toRingHom hx
  · simp only [finiteGlobalPointAction_contraction, Category.assoc, olderGlobalChart_cubic]
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      CommRingCat.ofHom_comp, Spec.map_comp,
      Category.assoc] using hadd.symm
  · rw [Category.assoc, olderGlobalChart_cubic]
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth

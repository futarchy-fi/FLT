/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteGenericChartEvaluation

/-!
# Original chart multiplication and inversion after generic base change

The actual pullback adjunction preserves the identity-group operations.
The projection formulas identify each original chart with translation by
its original cyclic section in the independently compared generic group.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj GrpObj
open CartesianMonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
open GroupObjectPointTranslation GroupSchemePointAdjunction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic completeRotation translation
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))
local notation "s" => Spec.map (CommRingCat.ofHom a)
local notation "G" => completePointOriginalBaseGroup K n h (0 : Fin n)
local notation "H" => Functor.obj (Functor.mapCommGrp (Over.pullback s)) (G)
local notation "u" => Scheme.Opens.ι (completePointIdentityOpen K n h (0 : Fin n))
local notation "π" => exactVeroneseProjToBase K n h
variable {T : Over (Spec (.of L))}
local notation "e" => pointsEquiv s (completePointOriginalBaseGroup K n h (0 : Fin n)) T
attribute [local instance] exactVeroneseProjToBase_lfp

/-- The unchanged projection from the actual generic identity group to the whole polygon. -/
def completeGenericOriginalProjection : (H).X.left ⟶ exactVeroneseProj K n h :=
  pullback.fst (G).X.hom s ≫ u

local notation "P" => completeGenericOriginalProjection K n h L a
attribute [local irreducible] completePointOriginalBaseGroup

/-- Multiplication in the original chart coordinates is the sum-label translated product. -/
theorem completeGenericChartMul_evaluation (b c : ZMod n) (x y : T ⟶ (H).X) :
    (lift ((e).symm x) ((e).symm y) ≫
      completeIdentityChartMul K n h 0 b c).left ≫ (π).smoothLocus.ι =
        ((x ≫ translation (completePointGenericCyclicPoint K n h L a ha p q hs b)) *
          (y ≫ translation (completePointGenericCyclicPoint K n h L a ha p q hs c))).left ≫
            P := by
  change (lift ((e).symm x) ((e).symm y) ≫ μ[(G).X] ≫
    completeIdentityChart K n h 0 (b + c)).left ≫ (π).smoothLocus.ι = _
  rw [← Category.assoc]
  calc
    _ = (((e).symm (x * y)) ≫ completeIdentityChart K n h 0 (b + c)).left ≫
        (π).smoothLocus.ι :=
      congrArg (fun z : (Over.map s).obj T ⟶ (G).X ↦
        (z ≫ completeIdentityChart K n h 0 (b + c)).left ≫ (π).smoothLocus.ι)
          ((e).symm.map_mul x y).symm
    _ = _ := (completeGenericChart_evaluation K n h L a ha p q hs (b + c) (x * y)).trans
      (congrArg (fun z : T ⟶ (H).X ↦ z.left ≫ P)
        (completePointGenericTranslation_mul K n h L a ha p q hs b c x y).symm)

/-- Original chart inversion is inversion after translation in the actual generic group. -/
theorem completeGenericChartInv_evaluation (b : ZMod n) (x : T ⟶ (H).X) :
    (((e).symm x) ≫ completeIdentityChartInv K n h 0 b).left ≫ (π).smoothLocus.ι =
      (x ≫ translation (completePointGenericCyclicPoint K n h L a ha p q hs b))⁻¹.left ≫
        P := by
  change (((e).symm x) ≫ ι[(G).X] ≫
    completeIdentityChart K n h 0 (-b)).left ≫ (π).smoothLocus.ι = _
  rw [← Category.assoc]
  calc
    _ = (((e).symm x⁻¹) ≫ completeIdentityChart K n h 0 (-b)).left ≫
        (π).smoothLocus.ι :=
      congrArg (fun z : (Over.map s).obj T ⟶ (G).X ↦
        (z ≫ completeIdentityChart K n h 0 (-b)).left ≫ (π).smoothLocus.ι)
          (map_inv (e).symm x).symm
    _ = _ := (completeGenericChart_evaluation K n h L a ha p q hs (-b) x⁻¹).trans
      (congrArg (fun z : T ⟶ (H).X ↦ z.left ≫ P)
        (completePointGenericTranslation_inv K n h L a ha p q hs b x).symm)

end FLT.Mazur.PolygonInfinitesimalStages

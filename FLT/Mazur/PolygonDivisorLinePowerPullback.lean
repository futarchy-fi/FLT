/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorLineBundlePower
public import FLT.Mazur.PolygonDivisorLinePullback
public import FLT.Mazur.ProjectiveLineMarkedPullbackCoordinates

/-!
# Polygon divisor powers on normalization and affine charts

Transport through the actual tensor-power comparison identifies O(mD) with
the marked power on each normalization component and then on both affine
charts. These isomorphisms yield coordinates on actual sections. Their
Laurent transition and common-node-fiber compatibility remain separate.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve.ModuleLineBundleTensorPullback
variable {X : Scheme.{u}} {M N : X.Modules}
/-- Tensor powers carry actual module isomorphisms to module isomorphisms. -/
def divisorTensorPowerCongr (e : M ≅ N) : ∀ m : ℕ, tensorPower M m ≅ tensorPower N m
  | 0 => Iso.refl _
  | m + 1 => ModuleSheafTensor.congr e (divisorTensorPowerCongr e m)
/-- Degree zero preserves the structure module. -/
@[simp]
lemma tensorPowerCongr_zero (e : M ≅ N) : divisorTensorPowerCongr e 0 = Iso.refl _ := rfl
/-- The successor comparison tensors the original isomorphism with the previous power. -/
@[simp]
lemma tensorPowerCongr_succ (e : M ≅ N) (m : ℕ) :
    divisorTensorPowerCongr e (m + 1) = ModuleSheafTensor.congr e (divisorTensorPowerCongr e m) := rfl
end FLT.Mazur.FCurve.ModuleLineBundleTensorPullback
namespace FLT.Mazur.PolygonDivisorLineComparison
open PolygonPinching PolygonDivisorNormalizationPullback FCurve
open ModuleLineBundleTensorPullback
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

/-- Every positive divisor power pulls back to the marked divisor power on a component. -/
def linePowerIso (a : Fin n → Kˣ) (i : Fin n) (m : ℕ) :
    (Scheme.Modules.pullback (componentι K n i ≫ p).left).obj
      (divisorLineBundle (PolygonBoundaryDivisor.ideal K n p a ^ m)
        ((PolygonBoundaryDivisor.cartier K n p hn q h a).1.pow m)) ≅
      divisorLineBundle ((markedPoint K (a i)).ker ^ m)
        ((ProjectiveLineMarkedCharts.relativeCartier K (a i)).1.pow m) :=
  (Scheme.Modules.pullback (componentι K n i ≫ p).left).mapIso
      (divisorLineBundlePowerIso (PolygonBoundaryDivisor.cartier K n p hn q h a).1 m).symm ≪≫
    tensorPowerIso (componentι K n i ≫ p).left _ m ≪≫
    divisorTensorPowerCongr (lineIso K n hn p q h a i) m ≪≫
    divisorLineBundlePowerIso (ProjectiveLineMarkedCharts.relativeCartier K (a i)).1 m

/-- The actual polygon divisor power on the left affine chart. -/
def leftChartPowerIso (a : Fin n → Kˣ) (i : Fin n) (m : ℕ) :
    (Scheme.Modules.pullback
      (ProjectiveLine.left K ≫ (componentι K n i ≫ p).left)).obj
      (divisorLineBundle (PolygonBoundaryDivisor.ideal K n p a ^ m)
        ((PolygonBoundaryDivisor.cartier K n p hn q h a).1.pow m)) ≅
      divisorLineBundle ((ProjectiveLineMarkedCharts.chartPoint K (a i : Kˣ)).ker ^ m)
        ((ProjectiveLineMarkedDualCoordinates.effectiveCartier K (a i : Kˣ)).pow m) :=
  (Scheme.Modules.pullbackComp (ProjectiveLine.left K) (componentι K n i ≫ p).left).symm.app _ ≪≫
    (Scheme.Modules.pullback (ProjectiveLine.left K)).mapIso (linePowerIso K n hn p q h a i m) ≪≫
    ProjectiveLineMarkedPullbackCoordinates.leftPowerIso K (a i) m

/-- Coordinates on arbitrary sections of the polygon power pulled to the left chart. -/
def leftChartSectionsCoordinate (a : Fin n → Kˣ) (i : Fin n) (m : ℕ) :=
  ModuleSheafTensor.sectionsCongr (leftChartPowerIso K n hn p q h a i m) ⊤ ≪≫ₗ
    ProjectiveLineMarkedDualCoordinates.sectionsCoordinate K (a i : Kˣ) m

/-- The actual polygon divisor power on the right affine chart. -/
def rightChartPowerIso (a : Fin n → Kˣ) (i : Fin n) (m : ℕ) :
    (Scheme.Modules.pullback
      (ProjectiveLine.right K ≫ (componentι K n i ≫ p).left)).obj
      (divisorLineBundle (PolygonBoundaryDivisor.ideal K n p a ^ m)
        ((PolygonBoundaryDivisor.cartier K n p hn q h a).1.pow m)) ≅
      divisorLineBundle ((ProjectiveLineMarkedCharts.chartPoint K ((a i)⁻¹ : Kˣ)).ker ^ m)
        ((ProjectiveLineMarkedDualCoordinates.effectiveCartier K ((a i)⁻¹ : Kˣ)).pow m) :=
  (Scheme.Modules.pullbackComp (ProjectiveLine.right K) (componentι K n i ≫ p).left).symm.app _ ≪≫
    (Scheme.Modules.pullback (ProjectiveLine.right K)).mapIso (linePowerIso K n hn p q h a i m) ≪≫
    ProjectiveLineMarkedPullbackCoordinates.rightPowerIso K (a i) m

/-- Coordinates on arbitrary sections of the polygon power pulled to the right chart. -/
def rightChartSectionsCoordinate (a : Fin n → Kˣ) (i : Fin n) (m : ℕ) :=
  ModuleSheafTensor.sectionsCongr (rightChartPowerIso K n hn p q h a i m) ⊤ ≪≫ₗ
    ProjectiveLineMarkedDualCoordinates.sectionsCoordinate K ((a i)⁻¹ : Kˣ) m
end FLT.Mazur.PolygonDivisorLineComparison

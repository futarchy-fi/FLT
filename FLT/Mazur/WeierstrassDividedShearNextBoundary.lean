/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedShearPreviousBoundary
public import FLT.Mazur.WeierstrassSuccessiveXShearGluing

/-!
# Shearing the original deeper boundary and depth transition

The next divided depth retains the forced uniformizer-power identification.
The whole successive pushout then proves compatibility of its deeper attachment.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R}
  {k : ℕ} (e : Data W π (k + 1)) (r : R)
local notation "U" => rootShearCurve W r
local notation "m" => WeierstrassSuccessiveX.shearModificationIso W (π ^ k) π e.b3 e.b4 e.b6 r

/-- The deeper chart shear retains the original power-normalized chart inclusion. -/
@[reassoc] theorem shear_depthDividedChart :
    WeierstrassSuccessiveX.depthDividedChart π k U e.b3 (e.b4 - r * e.b3) e.b6 ≫ (m).hom =
      (shearChartIso e r).hom ≫
        WeierstrassSuccessiveX.depthDividedChart π k W e.b3 e.b4 e.b6 := by
  have h : (WeierstrassDilatation.shearForward W (π ^ (k + 1)) e.b3 e.b4 e.b6 r).comp
      (WeierstrassSuccessiveX.nextDepthEquiv π k W e.b3 e.b4 e.b6).toAlgHom =
      (WeierstrassSuccessiveX.nextDepthEquiv π k U e.b3 (e.b4 - r * e.b3) e.b6
        ).toAlgHom.comp
          (WeierstrassDilatation.shearForward W (π ^ k * π) e.b3 e.b4 e.b6 r) := by
    apply WeierstrassDilatation.hom_ext <;>
      simp [WeierstrassSuccessiveX.nextDepthEquiv]
  rw [WeierstrassSuccessiveX.depthDividedChart, Category.assoc,
    WeierstrassSuccessiveX.shearModificationIso_divided]
  rw [WeierstrassSuccessiveX.depthDividedChart, ← Category.assoc, ← Category.assoc]
  congr 1
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom)) h.symm

/-- The original deeper-boundary attachment itself commutes with shear. -/
@[reassoc] theorem shearStepXIso_nextToX :
    nextToX (shearData e r) ≫ (shearStepXIso e r).hom =
      (shearBoundaryIso e r).hom ≫ nextToX e := by
  apply (cancel_mono (WeierstrassSuccessiveX.xChart W (π ^ k) π e.b3 e.b4 e.b6)).mp
  have hx : (shearStepXIso e r).hom ≫
      WeierstrassSuccessiveX.xChart W (π ^ k) π e.b3 e.b4 e.b6 =
      WeierstrassSuccessiveX.xChart U (π ^ k) π e.b3 (e.b4 - r * e.b3) e.b6 ≫ (m).hom :=
    (WeierstrassSuccessiveX.shearModificationIso_incidence W
      (π ^ k) π e.b3 e.b4 e.b6 r).symm
  rw [Category.assoc, hx, ← Category.assoc]
  erw [nextToX_chart (shearData e r)]
  erw [Category.assoc,
    shear_depthDividedChart e r, ← Category.assoc, ← shearBoundaryIso_inclusion e r,
    Category.assoc, ← nextToX_chart e, Category.assoc]
  simp only [nextToX, Category.assoc]

variable [IsDomain R] (hπ : π ≠ 0) (d : Data W π k)
local notation "F" => WeierstrassDilatation.depthTransition π k (k + 1) hπ (Nat.le_succ k)
  W d.b3 d.b4 d.b6 e.b3 e.b4 e.b6 d.factor3 d.factor4 d.factor6
  e.factor3 e.factor4 e.factor6
local notation "G" => WeierstrassDilatation.depthTransition π k (k + 1) hπ (Nat.le_succ k)
  U d.b3 (d.b4 - r * d.b3) d.b6 e.b3 (e.b4 - r * e.b3) e.b6
  (Data.factor3 (shearData d r)) (Data.factor4 (shearData d r))
  (Data.factor6 (shearData d r)) (Data.factor3 (shearData e r))
  (Data.factor4 (shearData e r)) (Data.factor6 (shearData e r))

/-- The full normalized divided-depth transition commutes with shear. -/
@[reassoc] theorem shearChartIso_transition :
    (shearChartIso e r).hom ≫ transition hπ d e =
      transition hπ (shearData d r) (shearData e r) ≫ (shearChartIso d r).hom := by
  have h : (WeierstrassDilatation.shearForward W (π ^ (k + 1)) e.b3 e.b4 e.b6 r).comp F =
      (G).comp (WeierstrassDilatation.shearForward W (π ^ k) d.b3 d.b4 d.b6 r) := by
    apply WeierstrassDilatation.hom_ext
    · simp
    · simp [mul_add, mul_left_comm]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom)) h

end FLT.Mazur.WeierstrassDividedDepth

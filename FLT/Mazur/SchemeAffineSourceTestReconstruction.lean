/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineSourceTestRecovery
public import FLT.Mazur.SchemeAffineCoverTestRecovery

/-!
# Source reconstruction in affine chart coordinates

An arbitrary scheme test of original source recovery is expressed in the
same base-chart and reconstruction coordinates as common-cover descent.
The formula retains the source path and its comparison to the base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
open SheafPullbackPathComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y W : Scheme.{u}} {p : Y ⟶ X} {ι : Type u}
variable (C : ι → SourceChart p) {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [∀ i, ((pullback (C i).chart.cover).obj M).IsQuasicoherent]
attribute [local irreducible] openGlued Chart.sheaf Chart.reconstruction
  openGluedChartIso chartTestRecoveryIso sourceRecoveryIso coverRecoveryIso

/-- Source recovery on a test is the original base-chart reconstruction with its paths. -/
@[reassoc]
lemma sourceRecoveryIso_test_reconstruction (i : ι) (t : W ⟶ (C i).source)
    (b : W ⟶ Spec (C i).chart.coverRing) (hb : t ≫ (C i).lift = b)
    (d : W ⟶ Y) (hd : t ≫ (C i).sourceMap = d)
    (hbd : b ≫ (C i).chart.cover = d)
    (f : W ⟶ Spec (C i).chart.baseRing) (hf : b ≫ Spec.map (C i).chart.ringMap = f)
    (z : W ⟶ X) (hz : d ≫ p = z) (hfa : f ≫ (C i).chart.base = z) :
    (pullback t).map (sourceRecoveryIso C D i).hom ≫
        (comparison t (C i).sourceMap d hd).hom.app M =
      (comparison t (C i).sourceMap d hd).hom.app
          ((pullback p).obj (openGlued (fun j ↦ (C j).chart) D)) ≫
        (comparison d p z hz).hom.app (openGlued (fun j ↦ (C j).chart) D) ≫
        (chartTestRecoveryIso (fun j ↦ (C j).chart) D i z f hfa).hom ≫
        (comparison b (Spec.map (C i).chart.ringMap) f hf).inv.app ((C i).chart.sheaf D) ≫
        (pullback b).map ((C i).chart.reconstruction D).hom ≫
        (comparison b (C i).chart.cover d hbd).hom.app M := by
  rw [sourceRecoveryIso_test C D i t b hb d hd hbd,
    coverRecoveryIso_test (fun j ↦ (C j).chart) D i b d f z hbd hf hz hfa]

end FLT.Mazur.SchemeAffineDescent

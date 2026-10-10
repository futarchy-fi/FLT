/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineSourceRecoveryNormalization
public import FLT.Mazur.SchemeAffineCoverTestTransport

/-!
# Source recovery preserves original transport on affine tests

Transfer the covering transport equation through the source-chart
normalization. The two source maps remain independent over the common base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
open SheafPullbackPathComparison SheafPullbackMapNormalization
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {ι : Type u}
variable (C : ι → SourceChart p) {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [∀ i, ((pullback (C i).chart.cover).obj M).IsQuasicoherent]
attribute [local irreducible] openGlued Chart.sheaf coverRecoveryIso

/-- Source recovery intertwines the original transport on independent affine source tests. -/
lemma sourceRecoveryIso_affine_test_transport (i j : ι) {A : CommRingCat.{u}}
    (t : Spec A ⟶ (C i).source) (v : Spec A ⟶ (C j).source)
    (d d' : Spec A ⟶ Y) (z : Spec A ⟶ X)
    (ht : t ≫ (C i).sourceMap = d) (hv : v ≫ (C j).sourceMap = d')
    (hz : d ≫ p = z) (hz' : d' ≫ p = z) :
    (comparison d p z hz).inv.app (openGlued (fun k ↦ (C k).chart) D) ≫
        normalize t (C i).sourceMap (C i).sourceMap d d ht ht
          (sourceRecoveryIso C D i).hom ≫
        (D.transport d d' (hz.trans hz'.symm)).hom =
      (comparison d' p z hz').inv.app (openGlued (fun k ↦ (C k).chart) D) ≫
        normalize v (C j).sourceMap (C j).sourceMap d' d' hv hv
          (sourceRecoveryIso C D j).hom := by
  have hb : (t ≫ (C i).lift) ≫ (C i).chart.cover = d := by
    rw [Category.assoc, SourceChart.square, ht]
  have hc : (v ≫ (C j).lift) ≫ (C j).chart.cover = d' := by
    rw [Category.assoc, SourceChart.square, hv]
  rw [sourceRecoveryIso_normalize_test C D i t (t ≫ (C i).lift) rfl d ht hb,
    sourceRecoveryIso_normalize_test C D j v (v ≫ (C j).lift) rfl d' hv hc]
  exact coverRecoveryIso_affine_test_transport (fun k ↦ (C k).chart) D i j
    (t ≫ (C i).lift) (v ≫ (C j).lift) d d' z hb hc hz hz'

end FLT.Mazur.SchemeAffineDescent

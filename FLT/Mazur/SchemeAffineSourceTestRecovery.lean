/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineSourceRecovery
public import FLT.Mazur.SheafPullbackMapNormalization

/-!
# Original source recovery on arbitrary scheme tests

The source-open reconstruction, tested on any scheme, is the normalized
pullback of the original covering-chart reconstruction. This retains the
actual source map and avoids an affineness assumption on source overlaps.
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
attribute [local irreducible] openGlued Chart.sheaf coverRecoveryIso

/-- A scheme test of source recovery retains its original covering-chart coordinates. -/
@[reassoc]
lemma sourceRecoveryIso_test (i : ι) (t : W ⟶ (C i).source)
    (b : W ⟶ Spec (C i).chart.coverRing) (hb : t ≫ (C i).lift = b)
    (d : W ⟶ Y) (hd : t ≫ (C i).sourceMap = d)
    (hbd : b ≫ (C i).chart.cover = d) :
    (pullback t).map (sourceRecoveryIso C D i).hom ≫
        (comparison t (C i).sourceMap d hd).hom.app M =
      (comparison t (C i).sourceMap d hd).hom.app
          ((pullback p).obj (openGlued (fun j ↦ (C j).chart) D)) ≫
        SheafPullbackMapNormalization.normalize b (C i).chart.cover (C i).chart.cover
          d d hbd hbd (coverRecoveryIso (fun j ↦ (C j).chart) D i).hom := by
  exact SheafPullbackMapNormalization.normalize_refine
    (C i).lift (C i).chart.cover (C i).chart.cover
    (C i).sourceMap (C i).sourceMap (C i).square (C i).square
    t b hb d d hd hd hbd hbd (coverRecoveryIso (fun j ↦ (C j).chart) D i).hom

end FLT.Mazur.SchemeAffineDescent

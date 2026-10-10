/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineSourceTestRecovery

/-!
# Normalized source recovery on tests

Normalized source recovery equals normalized covering recovery on every
test. The equation uses only pullback path normalization.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
open SheafPullbackPathComparison SheafPullbackMapNormalization
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y W : Scheme.{u}} {p : Y ⟶ X} {ι : Type u}
variable (C : ι → SourceChart p) {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [∀ i, ((pullback (C i).chart.cover).obj M).IsQuasicoherent]
attribute [local irreducible] openGlued Chart.sheaf coverRecoveryIso

/-- Path normalization identifies source recovery with its actual covering recovery. -/
lemma sourceRecoveryIso_normalize_test (i : ι) (t : W ⟶ (C i).source)
    (b : W ⟶ Spec (C i).chart.coverRing) (hb : t ≫ (C i).lift = b)
    (d : W ⟶ Y) (hd : t ≫ (C i).sourceMap = d)
    (hbd : b ≫ (C i).chart.cover = d) :
    normalize t (C i).sourceMap (C i).sourceMap d d hd hd
        (sourceRecoveryIso C D i).hom =
      normalize b (C i).chart.cover (C i).chart.cover d d hbd hbd
        (coverRecoveryIso (fun j ↦ (C j).chart) D i).hom := by
  apply (cancel_epi ((comparison t (C i).sourceMap d hd).hom.app
    ((pullback p).obj (openGlued (fun j ↦ (C j).chart) D)))).mp
  rw [normalize_comm, sourceRecoveryIso_test C D i t b hb d hd hbd]

end FLT.Mazur.SchemeAffineDescent

/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineSourceRecoveryNormalization
public import FLT.Mazur.SchemeAffineCoverRecoveryCompatibility
public import FLT.Mazur.ModuleSheafAffineTestCompatibility

/-!
# Compatibility of source recovery on affine tests

Normalized source recovery equals normalized covering recovery on every
test. Affine tests with the same original source map therefore agree,
using the constructed common cover and its section.
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

/-- Affine tests of two source recoveries agree along their common original source map. -/
lemma sourceRecoveryIso_affine_test_compatible (i j : ι) {A : CommRingCat.{u}}
    (t : Spec A ⟶ (C i).source) (v : Spec A ⟶ (C j).source)
    (d : Spec A ⟶ Y) (ht : t ≫ (C i).sourceMap = d)
    (hv : v ≫ (C j).sourceMap = d) :
    normalize t (C i).sourceMap (C i).sourceMap d d ht ht
        (sourceRecoveryIso C D i).hom =
      normalize v (C j).sourceMap (C j).sourceMap d d hv hv
        (sourceRecoveryIso C D j).hom := by
  have hb : (t ≫ (C i).lift) ≫ (C i).chart.cover = d := by
    rw [Category.assoc, SourceChart.square, ht]
  have hc : (v ≫ (C j).lift) ≫ (C j).chart.cover = d := by
    rw [Category.assoc, SourceChart.square, hv]
  rw [sourceRecoveryIso_normalize_test C D i t (t ≫ (C i).lift) rfl d ht hb,
    sourceRecoveryIso_normalize_test C D j v (v ≫ (C j).lift) rfl d hv hc]
  exact coverRecoveryIso_affine_test_compatible (fun k ↦ (C k).chart) D i j
    (t ≫ (C i).lift) (v ≫ (C j).lift) d hb hc

/-- Original source recovery satisfies overlap compatibility for open gluing. -/
lemma sourceRecoveryIso_compatible :
    ModuleSheafOpenImmersionGluing.Compatible (fun i ↦ (C i).source)
      (fun i ↦ (C i).sourceMap) (fun i ↦ (sourceRecoveryIso C D i).hom) := by
  apply ModuleSheafOpenImmersionGluing.compatible_of_affine_tests
  intro i j A t v d ht hv
  exact sourceRecoveryIso_affine_test_compatible C D i j t v d ht hv

end FLT.Mazur.SchemeAffineDescent

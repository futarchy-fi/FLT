/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineSourceRecoveryTransport
public import FLT.Mazur.SchemeAffineSourceGlobalRecovery
public import FLT.Mazur.SheafPullbackMapNormalizationNaturality

/-!
# Global source recovery preserves transport on affine chart tests

The actual global recovery satisfies the original transport equation on
affine tests factoring through two independent source charts.
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

variable (hcover : ∀ y : Y, ∃ i, y ∈ Set.range (C i).sourceMap)

/-- Global recovery intertwines original transport on affine tests of two source charts. -/
lemma sourceGluedRecoveryIso_affine_test_transport (i j : ι) {A : CommRingCat.{u}}
    (t : Spec A ⟶ (C i).source) (v : Spec A ⟶ (C j).source)
    (d d' : Spec A ⟶ Y) (z : Spec A ⟶ X)
    (ht : t ≫ (C i).sourceMap = d) (hv : v ≫ (C j).sourceMap = d')
    (hz : d ≫ p = z) (hz' : d' ≫ p = z) :
    (comparison d p z hz).inv.app (openGlued (fun k ↦ (C k).chart) D) ≫
        (pullback d).map (sourceGluedRecoveryIso C D hcover).hom ≫
        (D.transport d d' (hz.trans hz'.symm)).hom =
      (comparison d' p z hz').inv.app (openGlued (fun k ↦ (C k).chart) D) ≫
        (pullback d').map (sourceGluedRecoveryIso C D hcover).hom := by
  have h := sourceRecoveryIso_affine_test_transport C D i j t v d d' z ht hv hz hz'
  rw [← sourceGluedRecoveryIso_pullback C D hcover i,
    ← sourceGluedRecoveryIso_pullback C D hcover j,
    normalize_pullback_map, normalize_pullback_map] at h
  exact h

end FLT.Mazur.SchemeAffineDescent

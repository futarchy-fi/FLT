/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineSourceGlobalTestTransport
public import FLT.Mazur.SchemeSourceTestOverlapRecognition

/-!
# Global source recovery identifies the original descent overlap

The constructed recovery satisfies the original transport equation on all
affine source tests. Those tests identify its canonical overlap with the
original descent datum, completing object recovery with overlap compatibility.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
open SchemePullbackOverlap
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {ι : Type u}
variable (C : ι → SourceChart p) {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [∀ i, ((pullback (C i).chart.cover).obj M).IsQuasicoherent]
variable (hcover : ∀ y : Y, ∃ i, y ∈ Set.range (C i).sourceMap)
attribute [local irreducible] openGlued Chart.sheaf coverRecoveryIso

/-- The actual global reconstruction induces precisely the original descent overlap. -/
lemma sourceGluedRecoveryIso_overlap :
    D.overlap = chartOverlap p (Limits.pullback.fst p p) (Limits.pullback.snd p p)
      (Limits.pullback.fst p p ≫ p) rfl Limits.pullback.condition.symm
      (openGlued (fun i ↦ (C i).chart) D) (sourceGluedRecoveryIso C D hcover) := by
  apply D.overlap_eq_chartOverlap_of_affine_source_tests
    (sourceGluedRecoveryIso C D hcover)
    (Scheme.Cover.mkOfCovers ι (fun i ↦ (C i).source) (fun i ↦ (C i).sourceMap) hcover)
  intro i j A a b d d' z ha hb hz hz'
  exact sourceGluedRecoveryIso_affine_test_transport C D hcover i j a b d d' z ha hb hz hz'

end FLT.Mazur.SchemeAffineDescent

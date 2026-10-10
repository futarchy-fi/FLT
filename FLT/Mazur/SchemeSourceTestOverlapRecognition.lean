/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafAffinePairTestDetection
public import FLT.Mazur.SchemeDescentTransportTest
public import FLT.Mazur.SchemeNormalizedRecoveryOverlap
public import FLT.Mazur.SchemeOverlapConjugation

/-!
# Recognizing original descent overlaps by affine source tests

Pullbacks of the source cover on both projections provide enough affine
tests to identify the actual descent overlap with reconstructed transport.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u v
namespace FLT.Mazur.SchemeGeometricDescent.Data
open SheafPullbackPathComparison SchemePullbackOverlap
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {M : Y.Modules} (D : Data p M)
variable {G : X.Modules} (e : (pullback p).obj G ≅ M) (U : Y.OpenCover.{v})

/-- Affine source tests identify the original descent overlap with reconstructed overlap. -/
lemma overlap_eq_chartOverlap_of_affine_source_tests
    (h : ∀ i j {A : CommRingCat.{u}} (a : Spec A ⟶ U.X i) (b : Spec A ⟶ U.X j)
      (d d' : Spec A ⟶ Y) (z : Spec A ⟶ X)
      (_ha : a ≫ U.f i = d) (_hb : b ≫ U.f j = d')
      (hz : d ≫ p = z) (hz' : d' ≫ p = z),
      (comparison d p z hz).inv.app G ≫ (pullback d).map e.hom ≫
          (D.transport d d' (hz.trans hz'.symm)).hom =
        (comparison d' p z hz').inv.app G ≫ (pullback d').map e.hom) :
    D.overlap = chartOverlap p (Limits.pullback.fst p p) (Limits.pullback.snd p p)
      (Limits.pullback.fst p p ≫ p) rfl Limits.pullback.condition.symm G e := by
  apply Iso.ext
  apply ModuleSheafOpenImmersionGluing.hom_ext_of_affine_pair_tests U U
    (Limits.pullback.fst p p) (Limits.pullback.snd p p)
  intro i j A t a b ha hb
  have hl : (t ≫ Limits.pullback.fst p p) ≫ p = t ≫ (Limits.pullback.fst p p ≫ p) :=
    Category.assoc _ _ _
  have hr : (t ≫ Limits.pullback.snd p p) ≫ p = t ≫ (Limits.pullback.fst p p ≫ p) := by
    rw [Category.assoc, Limits.pullback.condition]
  have ht := eq_chartOverlap_of_normalized_recovery p _ _ _ hl hr e _
    (h i j a b _ _ _ ha hb hl hr)
  have hn := (D.normalize_overlap_eq_transport t _ _ rfl rfl (hl.trans hr.symm)).trans
    (ht.trans (normalize_chartOverlap p _ _ _ rfl Limits.pullback.condition.symm
      t _ _ rfl rfl hl hr G e).symm)
  apply (cancel_mono ((comparison t (Limits.pullback.snd p p)
    (t ≫ Limits.pullback.snd p p) rfl).hom.app M)).mp
  apply (cancel_epi ((comparison t (Limits.pullback.fst p p)
    (t ≫ Limits.pullback.fst p p) rfl).inv.app M)).mp
  exact congrArg Iso.hom hn

end FLT.Mazur.SchemeGeometricDescent.Data

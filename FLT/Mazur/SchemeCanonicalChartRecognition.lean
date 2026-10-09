/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeCanonicalDescentData
public import FLT.Mazur.SchemeAffineChartRecognitionIso

/-!
# Canonical pullback descent recovers the base sheaf on affine charts

The identity reconstruction recognizes the canonical datum. Consequently each
affine chart of its effective descent is the original restricted base sheaf.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeGeometricDescent
open SchemePullbackOverlap
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} (p : Y ⟶ X) (A : X.Modules)

/-- The canonical datum is the reconstruction overlap of the identity chart. -/
lemma canonical_overlap_chart :
    (canonical p A).overlap = chartOverlap p (Limits.pullback.fst p p)
      (Limits.pullback.snd p p) (Limits.pullback.fst p p ≫ p)
      rfl Limits.pullback.condition.symm A (Iso.refl _) := by
  simp only [canonical, chartOverlap, Functor.mapIso_refl, Iso.refl_symm,
    Iso.refl_trans, Iso.trans_refl]

end FLT.Mazur.SchemeGeometricDescent

namespace FLT.Mazur.SchemeAffineDescent.Chart
open SchemeGeometricDescent
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} (C : Chart p) (A : X.Modules)
variable [((pullback C.base).obj A).IsQuasicoherent]
variable [((pullback C.cover).obj ((pullback p).obj A)).IsQuasicoherent]

/-- The canonical datum descends to the original base sheaf on this affine chart. -/
def canonicalRecognitionIso : (pullback C.base).obj A ≅ C.sheaf (canonical p A) :=
  C.recognitionIso (canonical p A) A (Iso.refl _) (canonical_overlap_chart p A)

/-- Canonical chart recognition reconstructs the actual pullback square comparison. -/
@[reassoc]
lemma canonicalRecognitionIso_reconstruction :
    (pullback (Spec.map C.ringMap)).map (C.canonicalRecognitionIso A).hom ≫
        (C.reconstruction (canonical p A)).hom =
      (SchemePullbackSquare.squareIso p (Spec.map C.ringMap)
        C.base C.cover C.square).hom.app A := by
  have h := C.recognitionIso_reconstruction (canonical p A) A (Iso.refl _)
    (canonical_overlap_chart p A)
  dsimp only [SchemeGeometricDescent.Data.recognitionChart] at h
  rw [Functor.mapIso_refl] at h
  exact h.trans (Category.comp_id _)

end FLT.Mazur.SchemeAffineDescent.Chart

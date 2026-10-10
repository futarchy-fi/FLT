/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineReconstructionRecognition
public import FLT.Mazur.SchemeAffineDescentChart

/-!
# Recovering a proposed base sheaf on each affine descent chart

The original overlap equation gives an actual isomorphism from the restricted
base sheaf to the effectively descended chart, with its reconstruction square.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
open SchemePullbackOverlap AffineGeometricDescentRecognition
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} (C : Chart p)
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable (A : X.Modules) (e : (pullback p).obj A ≅ M)
variable (he : D.overlap = chartOverlap p (Limits.pullback.fst p p)
  (Limits.pullback.snd p p) (Limits.pullback.fst p p ≫ p)
  rfl Limits.pullback.condition.symm A e)
variable [((pullback C.base).obj A).IsQuasicoherent]
variable [((pullback C.cover).obj M).IsQuasicoherent]

/-- Recognition identifies the restricted candidate with its actual affine descent. -/
def recognitionIso : (pullback C.base).obj A ≅ C.sheaf D :=
  sheafIso C.ringMap C.faithfullyFlat ((pullback C.base).obj A)
    (D.affineChart C.ringMap p C.base C.cover C.square)
    (SchemeGeometricDescent.Data.recognitionChart p A e C.ringMap C.base C.cover C.square)
    (D.affineChart_coactionCompatible p A e he C.ringMap C.base C.cover C.square)

/-- The recognition isomorphism retains the proposed reconstruction on the cover chart. -/
@[reassoc]
lemma recognitionIso_reconstruction :
    (pullback (Spec.map C.ringMap)).map (C.recognitionIso D A e he).hom ≫
      (C.reconstruction D).hom =
    (SchemeGeometricDescent.Data.recognitionChart p A e
      C.ringMap C.base C.cover C.square).hom :=
  sheafIso_reconstruction C.ringMap C.faithfullyFlat ((pullback C.base).obj A)
    (D.affineChart C.ringMap p C.base C.cover C.square)
    (SchemeGeometricDescent.Data.recognitionChart p A e C.ringMap C.base C.cover C.square)
    (D.affineChart_coactionCompatible p A e he C.ringMap C.base C.cover C.square)

/-- The prescribed cover reconstruction uniquely specifies the chart recognition map. -/
lemma recognitionIso_unique (f : (pullback C.base).obj A ⟶ C.sheaf D)
    (hf : (pullback (Spec.map C.ringMap)).map f ≫ (C.reconstruction D).hom =
      (SchemeGeometricDescent.Data.recognitionChart p A e
        C.ringMap C.base C.cover C.square).hom) :
    f = (C.recognitionIso D A e he).hom :=
  AffineQuasicoherentPullbackFaithful.reconstruction_unique C.ringMap C.faithfullyFlat
    (C.reconstruction D) f _ (hf.trans (C.recognitionIso_reconstruction D A e he).symm)

end FLT.Mazur.SchemeAffineDescent.Chart

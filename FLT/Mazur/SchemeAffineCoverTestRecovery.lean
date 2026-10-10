/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SheafPullbackTestReconstruction
public import FLT.Mazur.SchemeAffineChartTestRecovery
public import FLT.Mazur.SchemeAffineCoverRecovery

/-!
# Original covering recovery on scheme tests

The normalized original covering recovery is base-chart test recovery
followed by the original chart reconstruction. Its equation uses the
actual chart square and the actual glued object.
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

/-- The original covering pullback comparison is the comparison of the chart square. -/
lemma Chart.coverPullbackIso_eq_square (C : Chart p) :
    C.coverPullbackIso = SchemePullbackSquare.squareIso C.base C.cover p
      (Spec.map C.ringMap) C.square.symm := by
  apply Iso.ext
  simp only [Chart.coverPullbackIso, SchemePullbackSquare.squareIso,
    SheafPullbackPathComparison.comparison,
    Iso.trans_hom, Category.assoc]

variable (C : ι → Chart p) {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [∀ i, ((pullback (C i).cover).obj M).IsQuasicoherent]
variable [∀ i, IsOpenImmersion (C i).base]
attribute [local irreducible] openGlued Chart.sheaf Chart.reconstruction openGluedChartIso

/-- Cover recovery on a test factors through the actual base-chart reconstruction. -/
lemma coverRecoveryIso_test (i : ι) (t : W ⟶ Spec (C i).coverRing)
    (d : W ⟶ Y) (f : W ⟶ Spec (C i).baseRing) (z : W ⟶ X)
    (hd : t ≫ (C i).cover = d) (hf : t ≫ Spec.map (C i).ringMap = f)
    (hdp : d ≫ p = z) (hfa : f ≫ (C i).base = z) :
    normalize t (C i).cover (C i).cover d d hd hd (coverRecoveryIso C D i).hom =
      (comparison d p z hdp).hom.app (openGlued C D) ≫
        (chartTestRecoveryIso C D i z f hfa).hom ≫
        (comparison t (Spec.map (C i).ringMap) f hf).inv.app ((C i).sheaf D) ≫
        (pullback t).map ((C i).reconstruction D).hom ≫
        (comparison t (C i).cover d hd).hom.app M := by
  have h := SchemePullbackSquare.test_reconstruction p (Spec.map (C i).ringMap)
    (C i).base (C i).cover (C i).square.symm t d f z hd hf hdp hfa
    (openGluedChartIso C D i) ((C i).reconstruction D)
  simpa only [coverRecoveryIso, Chart.coverPullbackIso_eq_square,
    openGluedCoverChartIso, chartTestRecoveryIso, Iso.trans_hom, Iso.app_hom,
    Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom, Category.assoc] using h

end FLT.Mazur.SchemeAffineDescent

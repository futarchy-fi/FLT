/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafOverlapProjectionRecovery
public import FLT.Mazur.SchemeAffineTestProjectionComparison

/-!
# Chart reconstruction respects the effective scheme-test comparison

Normalize the original glued chart isomorphisms on an arbitrary common
scheme test. Their comparison is the independently constructed effective
descent map, as follows from the actual gluing projection equation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent
open SheafPullbackPathComparison ModuleSheafOverlapImageTransition
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y W : Scheme.{u}} {p : Y ⟶ X} {ι : Type u}
variable (C : ι → Chart p) {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [∀ i, ((pullback (C i).cover).obj M).IsQuasicoherent]
variable [∀ i, IsOpenImmersion (C i).base]
attribute [local irreducible] Chart.sheaf openGlued openGluedProjection

/-- Original chart recovery normalized on an arbitrary scheme test. -/
def chartTestRecoveryIso (i : ι) (a : W ⟶ X) (b : W ⟶ Spec (C i).baseRing)
    (hb : b ≫ (C i).base = a) :
    (pullback a).obj (openGlued C D) ≅ (pullback b).obj ((C i).sheaf D) :=
  (comparison b (C i).base a hb).symm.app (openGlued C D) ≪≫
    (pullback b).mapIso (openGluedChartIso C D i)

/-- The normalized chart recovery is computed from the original ambient projection. -/
lemma chartTestRecoveryIso_projection (i : ι) (a : W ⟶ X)
    (b : W ⟶ Spec (C i).baseRing) (hb : b ≫ (C i).base = a) :
    (chartTestRecoveryIso C D i a b hb).hom =
      (pullback a).map (openGluedProjection C D i) ≫
        (coordinateIso b (C i).base a hb ((C i).sheaf D)).hom :=
  coordinateIso_projection (C i).base (openGluedProjection C D i)
    (openGluedChartIso C D i) (openGluedChartIso_projection C D i) b a hb

/-- Actual chart reconstruction intertwines the independently constructed comparison. -/
@[reassoc]
lemma chartTestRecoveryIso_comparison (i j : ι) (a : W ⟶ X)
    (b : W ⟶ Spec (C i).baseRing) (c : W ⟶ Spec (C j).baseRing)
    (hb : b ≫ (C i).base = a) (hc : c ≫ (C j).base = a) :
    (chartTestRecoveryIso C D i a b hb).hom ≫
        (C i).schemeTestComparison (C j) D b c (hb.trans hc.symm) =
      (chartTestRecoveryIso C D j a c hc).hom := by
  have h := congrArg (fun f ↦ f ≫ (coordinateIso c (C j).base a hc ((C j).sheaf D)).hom)
    (openGluedProjection_schemeTest C D i j a b c hb hc)
  rw [chartTestRecoveryIso_projection, chartTestRecoveryIso_projection]
  simpa only [Chart.ambientTestComparison, Category.assoc, Iso.inv_hom_id,
    Category.comp_id] using h

end FLT.Mazur.SchemeAffineDescent

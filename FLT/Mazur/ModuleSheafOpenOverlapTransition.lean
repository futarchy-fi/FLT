/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafOverlapImageCoherence
public import FLT.Mazur.ModuleSheafOpenImageChart
public import FLT.Mazur.ModuleSheafLocalIsoTransport

/-!
# Chart transitions on specified ambient opens

Image-open comparisons can be indexed by the actual overlap open. Their
restriction and cocycle laws retain the original coordinate comparisons.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.ModuleSheafOpenOverlapTransition
open ModuleSheafOpenImageChart ModuleSheafMorphismGluing
open ModuleSheafOverlapImageTransition SheafPullbackPathComparison
universe u
variable {X Y Z : Scheme.{u}} (i : Y ⟶ X) (j : Z ⟶ X)
  [IsOpenImmersion i] [IsOpenImmersion j] {M : Y.Modules} {N : Z.Modules}
variable (U : X.Opens) (hi : U ≤ i.opensRange) (hj : U ≤ j.opensRange)
variable (e : (pullback (coordinate i U hi)).obj M ≅
  (pullback (coordinate j U hj)).obj N)

/-- The original coordinate transition extended to its specified overlap open. -/
def transition : ((pushforward i).obj M).over U ≅ ((pushforward j).obj N).over U :=
  cast (congrArg (fun V ↦ ((pushforward i).obj M).over V ≅
    ((pushforward j).obj N).over V) U.opensRange_ι)
      (ModuleSheafOverlapImageTransition.imageIso i j (coordinate i U hi)
        (coordinate j U hj) U.ι (coordinate_comp i U hi) (coordinate_comp j U hj) e)

/-- Index transport preserves every section map of the original image transition. -/
theorem transition_app (V : X.Opens) (hV : V ≤ U) :
    localApp (transition i j U hi hj e).hom hV =
      localApp (ModuleSheafOverlapImageTransition.imageIso i j (coordinate i U hi)
        (coordinate j U hj) U.ι (coordinate_comp i U hi) (coordinate_comp j U hj) e).hom
          (hV.trans_eq U.opensRange_ι.symm) := by
  unfold transition
  exact localApp_iso_cast U.opensRange_ι _ V hV

variable (V : X.Opens) (hV : V ≤ U)
variable (e' : (pullback (coordinate i V (hV.trans hi))).obj M ≅
  (pullback (coordinate j V (hV.trans hj))).obj N)

/-- Geometric restriction of coordinates restricts the same map on every smaller open. -/
theorem transition_refine_app
    (he : (pullback (X.homOfLE hV)).map e.hom ≫
        (comparison (X.homOfLE hV) (coordinate j U hj)
          (coordinate j V (hV.trans hj)) (coordinate_refine j hV hj)).hom.app N =
      (comparison (X.homOfLE hV) (coordinate i U hi)
          (coordinate i V (hV.trans hi)) (coordinate_refine i hV hi)).hom.app M ≫ e'.hom)
    (W : X.Opens) (hW : W ≤ V) :
    localApp (transition i j V (hV.trans hi) (hV.trans hj) e').hom hW =
      localApp (transition i j U hi hj e).hom (hW.trans hV) := by
  rw [transition_app, transition_app]
  exact imageIso_refine_app i j (coordinate i U hi) (coordinate j U hj) U.ι
    (coordinate_comp i U hi) (coordinate_comp j U hj) e (X.homOfLE hV)
    (coordinate i V (hV.trans hi)) (coordinate j V (hV.trans hj)) V.ι
    (coordinate_refine i hV hi) (coordinate_refine j hV hj) (X.homOfLE_ι hV)
    (coordinate_comp i V (hV.trans hi)) (coordinate_comp j V (hV.trans hj)) e' he W _ _

variable {Y' : Scheme.{u}} (k : Y' ⟶ X) [IsOpenImmersion k]
  (hk : U ≤ k.opensRange) {P : Y'.Modules}
  (f : (pullback (coordinate j U hj)).obj N ≅ (pullback (coordinate k U hk)).obj P)
  (g : (pullback (coordinate i U hi)).obj M ≅ (pullback (coordinate k U hk)).obj P)

/-- Actual coordinate cocycles give section cocycles on the specified overlap. -/
theorem transition_cocycle_app (hc : e.hom ≫ f.hom = g.hom)
    (W : X.Opens) (hW : W ≤ U) (a : Γ((pushforward i).obj M, W)) :
    localApp (transition j k U hj hk f).hom hW
        (localApp (transition i j U hi hj e).hom hW a) =
      localApp (transition i k U hi hk g).hom hW a := by
  rw [transition_app, transition_app, transition_app]
  exact imageIso_cocycle_app i j (coordinate i U hi) (coordinate j U hj) U.ι
    (coordinate_comp i U hi) (coordinate_comp j U hj) e k (coordinate k U hk)
    (coordinate_comp k U hk) f g hc W _ a

end FLT.Mazur.ModuleSheafOpenOverlapTransition

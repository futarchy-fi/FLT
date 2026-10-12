/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafOpenOverlapTransition
public import FLT.Mazur.ModuleSheafLocalEquation

/-!
# Original transition compatibility from coordinate quotient maps

An equality after the two original coordinate recoveries proves compatibility
of ambient maps on the actual overlap open.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.ModuleSheafOpenOverlapTransition
open ModuleSheafOpenImageChart ModuleSheafOverlapImageTransition
open ModuleSheafMorphismGluing ModuleSheafOpenImmersionLocalHom
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y Z : Scheme.{u}} (i : Y ⟶ X) (j : Z ⟶ X)
  [IsOpenImmersion i] [IsOpenImmersion j]
variable {S : X.Modules} {M : Y.Modules} {N : Z.Modules}
variable (U : X.Opens) (hi : U ≤ i.opensRange) (hj : U ≤ j.opensRange)
variable (e : (pullback (coordinate i U hi)).obj M ≅
  (pullback (coordinate j U hj)).obj N)

/-- Coordinate compatibility implies compatibility with the original image transition. -/
theorem transition_projection (q : S ⟶ (pushforward i).obj M)
    (q' : S ⟶ (pushforward j).obj N)
    (h : (pullback U.ι).map q ≫
        (coordinateIso (coordinate i U hi) i U.ι (coordinate_comp i U hi) M).hom ≫
          e.hom =
      (pullback U.ι).map q' ≫
        (coordinateIso (coordinate j U hj) j U.ι (coordinate_comp j U hj) N).hom) :
    q.over U ≫ (transition i j U hi hj e).hom = q'.over U := by
  have ha : (pullback U.ι).map q ≫
      (ambientIso i j (coordinate i U hi) (coordinate j U hj) U.ι
        (coordinate_comp i U hi) (coordinate_comp j U hj) e).hom =
      (pullback U.ι).map q' := by
    apply (cancel_mono
      (coordinateIso (coordinate j U hj) j U.ι (coordinate_comp j U hj) N).hom).mp
    simpa only [Category.assoc, ambientIso_coordinate] using h
  have hl := congrArg (localHom U.ι) ha
  rw [localHom_comp, localHom_map, localHom_map] at hl
  apply localEval_hom_ext
  intro W hW s
  rw [localEval_comp, localEval_over, localEval_over]
  unfold localEval
  rw [transition_app, imageIso_hom]
  have hh := localEval_projection q q' _ hl
    (hW.trans_eq U.opensRange_ι.symm) s
  simpa only [localEval] using hh

end FLT.Mazur.ModuleSheafOpenOverlapTransition

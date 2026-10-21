/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealModulePullbackCoherence

/-!
# Naturality of ideal equations in arbitrary commuting squares

The equation is the actual module map into the structure sheaf. The square
retains its source comparison even when the base change is not flat.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y Z W : Scheme.{u}} (I : Y.IdealSheafData)
  (f : X ⟶ Y) (g : Z ⟶ W) (i : Z ⟶ X) (j : W ⟶ Y) (h : i ≫ f = g ≫ j)

/-- The sheaf associator identifies the two paths around the actual scheme square. -/
def idealEquationSquareIso :
    (pullback i).obj ((pullback f).obj (idealModule I)) ≅
      (pullback g).obj ((pullback j).obj (idealModule I)) :=
  (SheafPullbackPathComparison.comparison i f (g ≫ j) h).app (idealModule I) ≪≫
    ((pullbackComp g j).app (idealModule I)).symm

/-- Pulling the equation around either side preserves the full module-sheaf map. -/
theorem idealModulePullbackι_square :
    (pullback i).map (idealModulePullbackι I f) ≫ (modulePullbackUnitIso i).hom =
      (idealEquationSquareIso I f g i j h).hom ≫
        (pullback g).map (idealModulePullbackHom I j) ≫
          idealModulePullbackι (I.comap j) g := by
  rw [idealModulePullbackι_comparison I i f (g ≫ j) h]
  have hc : (pullback g).map (idealModulePullbackHom I j) ≫
      idealModulePullbackι (I.comap j) g =
        (pullback g).map (idealModulePullbackι I j) ≫ (modulePullbackUnitIso g).hom := by
    rw [idealModulePullbackι, ← Category.assoc, ← Functor.map_comp,
      idealModulePullbackHom_ι]
  rw [hc, idealModulePullbackι_comp]
  simp only [idealEquationSquareIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Iso.app_inv, Category.assoc, Iso.inv_hom_id_app_assoc]

include h in
/-- The image ideals of the two equations agree on the entire square. -/
theorem idealEquationImage_square : (I.comap f).comap i = (I.comap j).comap g :=
  idealModulePullback_comap_square I f g i j h

end FLT.Mazur.FCurve

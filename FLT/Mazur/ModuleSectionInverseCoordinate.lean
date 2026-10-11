/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionUnit

/-!
# Coordinates of a generating section under its inverse

The inverse of the section morphism sends its restricted generator to one
on every open of the trivializing chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) (s : Γ(M, U))

/-- The section morphism sends one to the original section restricted to the subopen. -/
theorem sectionHom_app_one (V : U.toScheme.Opens) :
    (sectionHom M U s).app V (1 : Γ(U.toScheme, V)) =
      (M.restrictAppIso U.ι V).inv
        (M.presheaf.map (homOfLE (U.ι_image_le V)).op s) := by
  rw [sectionHom_app, map_one]
  rfl

variable [IsIso (sectionHom M U s)]

/-- The inverse generating morphism gives coordinate one to the actual generator. -/
theorem inverseSectionHom_app_section (V : U.toScheme.Opens) :
    (show Γ(U.toScheme, V) from (inv (sectionHom M U s)).app V
      ((M.restrictAppIso U.ι V).inv
        (M.presheaf.map (homOfLE (U.ι_image_le V)).op s))) = 1 := by
  rw [← sectionHom_app_one]
  exact congrArg (fun f ↦ f.app V (1 : Γ(U.toScheme, V)))
    (IsIso.hom_inv_id (sectionHom M U s))

end FLT.Mazur.FCurve

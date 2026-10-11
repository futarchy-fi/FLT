/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorIdealFunctionalSection

/-!
# Scalar coordinates of divisor functionals

Multiplication by a complement function in the ideal-dual presentation is
scalar multiplication of the actual canonical divisor section.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme} {I : X.IdealSheafData}

/-- Global scalars on an open act on its actual dual sections by precomposition. -/
theorem scalarEnd_dualSection (M : X.Modules) (U : X.Opens) (r : Γ(X, U))
    (φ : ModuleDualSections M U) :
    IdealPowerScalarLift.scalarEnd (M.restrict U.ι) (U.topIso.inv r) ≫ φ = r • φ := by
  ext V t
  rw [Hom.comp_app, ConcreteCategory.comp_apply, IdealPowerScalarLift.scalarEnd_app,
    Hom.app_smul, moduleDualSections_smul_app, Scheme.Opens.ι_appIso]
  congr 1
  change X.presheaf.map (U.ι.opensFunctor.map V.leTop).op
    (X.presheaf.map (eqToHom U.ι_image_top).op r) =
      X.presheaf.map (homOfLE (U.ι_image_le V)).op r
  rw [← Functor.map_comp_apply]
  rfl

/-- An included ideal followed by multiplication is a scalar canonical section. -/
theorem divisorFunctionalScalar_eq (hI : EffectiveCartier I) (U : X.Opens)
    (r : Γ(X, U)) :
    (restrictFunctor U.ι).map (idealModuleι I) ≫
      IdealPowerScalarLift.scalarEnd ((structureModule X).restrict U.ι) (U.topIso.inv r) ≫
        moduleDualUnitSection U 1 = r • divisorSection hI U := by
  rw [scalarEnd_dualSection, divisorSection_eq]
  ext V t
  rfl

end FLT.Mazur.FCurve

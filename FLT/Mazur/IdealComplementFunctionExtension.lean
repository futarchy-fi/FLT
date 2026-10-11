/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealPowerExtensionGluing
public import FLT.Mazur.IdealPowerScalarLift
public import FLT.Mazur.StructureIdealPowerQuotient

/-!
# Clearing the ideal denominator of an actual complement function

On a Noetherian scheme, a function off an ideal support extends to a
linear functional on a power of the original ideal module. The restriction
formula keeps both the original function and the original ideal inclusion.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.IdealComplementFunctionExtension
open FCurve GlobalIdealPower GlobalIdealPowerCompatibility
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme} [IsNoetherian X] (I : X.IdealSheafData)

/-- An open endomorphism of functions extends from an actual ideal power. -/
theorem exists_idealFunctional
    (g : (structureModule X).restrict (complement I).ι ⟶
      (structureModule X).restrict (complement I).ι) :
    ∃ n : ℕ, ∃ f : idealModule (I ^ n) ⟶ structureModule X,
      (restrictFunctor (complement I).ι).map f =
        (restrictFunctor (complement I).ι).map (idealModuleι (I ^ n)) ≫ g := by
  let _ := CoherentIdealIntersection.structureModule_coherent (X := X)
  obtain ⟨n, f, hf⟩ := IdealPowerExtensionGluing.exists_ideal_power_extension I
    (structureModule X) (structureModule X) g
  refine ⟨n, (StructureIdealPowerQuotient.multipleIso (I ^ n)).inv ≫ f, ?_⟩
  rw [Functor.map_comp, hf, ← Category.assoc, ← Functor.map_comp]
  congr 1
  rw [← StructureIdealPowerQuotient.multipleIso_inclusion, Iso.inv_hom_id_assoc]

/-- Every actual complement function has a global ideal-power denominator. -/
theorem exists_function_denominator (a : Γ((complement I).toScheme, ⊤)) :
    ∃ n : ℕ, ∃ f : idealModule (I ^ n) ⟶ structureModule X,
      (restrictFunctor (complement I).ι).map f =
        (restrictFunctor (complement I).ι).map (idealModuleι (I ^ n)) ≫
          IdealPowerScalarLift.scalarEnd ((structureModule X).restrict (complement I).ι) a :=
  exists_idealFunctional I _

end FLT.Mazur.IdealComplementFunctionExtension

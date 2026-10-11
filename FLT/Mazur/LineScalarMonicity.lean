/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalScalarCohomology
public import FLT.Mazur.ModuleLineTensorExact

/-!
# Regular scalars on an actual line sheaf

Tensor the regular scalar sequence of the structure sheaf with the line.
The unit comparison identifies its first map with the original scalar map
on the line, so regularity is preserved without choosing a global frame.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

namespace FLT.Mazur.LineScalarMonicity

open FCurve IdealPowerScalarLift ModuleSheafTensor

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme.{u}} (L : X.Modules) (r : Γ(X, ⊤))

/-- The left unit comparison retains scalar multiplication in the structure factor. -/
@[reassoc] theorem leftUnitor_scalar :
    ModuleSheafTensor.map (scalarEnd (structureModule X) r) (𝟙 L) ≫
      (leftUnitor L).hom = (leftUnitor L).hom ≫ scalarEnd L r := by
  apply ModuleSheafTensor.hom_ext
  intro U a l
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, map_pure,
    Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply, scalarEnd_app]
  erw [leftUnitor_pure, leftUnitor_pure]
  exact mul_smul _ _ _

/-- A scalar regular on the structure sheaf is regular on every locally free rank-one sheaf. -/
theorem scalarEnd_mono (hL : LocallyFreeRankOne L)
    [Mono (scalarEnd (structureModule X) r)] : Mono (scalarEnd L r) := by
  let hS := ModuleLineTensorExact.shortExact
    (PrincipalScalarCohomology.sequence (structureModule X) r)
    (PrincipalScalarCohomology.sequence_shortExact (structureModule X) r) L hL
  let _ : Mono (ModuleSheafTensor.map (scalarEnd (structureModule X) r) (𝟙 L)) := hS.mono_f
  have he : scalarEnd L r = (leftUnitor L).inv ≫
      ModuleSheafTensor.map (scalarEnd (structureModule X) r) (𝟙 L) ≫
        (leftUnitor L).hom := by
    rw [leftUnitor_scalar, Iso.inv_hom_id_assoc]
  rw [he]
  infer_instance

end FLT.Mazur.LineScalarMonicity

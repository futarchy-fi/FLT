/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineTensorCocycle

/-!
# Recognition of tensor descent data from their coalgebra

Equality of coefficient coactions determines the entire tensor descent datum.
The comparison stays at the module level before it is applied to sheaves.
-/

@[expose] public noncomputable section
open CategoryTheory
universe u
namespace FLT.Mazur.AffineTensorCocycle
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : CommRingCat.{u}} (φ : R ⟶ S) (N : ModuleCat.{u} S)

/-- Equality of the coalgebra maps determines the tensor overlap datum. -/
theorem datum_eq_of_coalgebra_map_eq :
    let := φ.hom.toAlgebra
    let := Module.compHom N φ.hom
    let : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
    ∀ D E : Datum R S N, (toCoalgebra φ N D).a = (toCoalgebra φ N E).a → D = E := by
  let := φ.hom.toAlgebra
  let := Module.compHom N φ.hom
  let : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  change ∀ D E : Datum R S N,
    (toCoalgebra φ N D).a = (toCoalgebra φ N E).a → D = E
  intro D E h
  have hc : D.coaction = E.coaction := congrArg ModuleCat.Hom.hom h
  have he := D.overlap_eq_of_coaction_eq hc
  cases D
  cases E
  cases he
  rfl

end FLT.Mazur.AffineTensorCocycle

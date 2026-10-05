/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineTensorCocycleTransport

/-!
# Canonical coefficient data for a reconstruction chart

A coefficient isomorphism from scalar extension transports the canonical
tensor datum. Its coaction intertwines the canonical comparison coalgebra.
-/

@[expose] public noncomputable section
open CategoryTheory TensorProduct
universe u
namespace FLT.Mazur.AffineTensorCocycle
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : CommRingCat.{u}} (φ : R ⟶ S) (P : ModuleCat.{u} R) (N : ModuleCat.{u} S)
variable (e : (ModuleCat.extendScalars φ.hom).obj P ≅ N)

/-- The tensor datum carried by a scalar-extension reconstruction chart. -/
def chartDatum :
    letI := φ.hom.toAlgebra
    letI := Module.compHom N φ.hom
    letI : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
    Datum R S N := by
  letI := φ.hom.toAlgebra
  letI := Module.compHom N φ.hom
  letI : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  exact transportDatum (canonicalDatum P) e.toLinearEquiv

/-- The coefficient chart intertwines the canonical and transported coactions. -/
theorem chartDatum_coaction :
    ((Comonad.comparison (ModuleCat.extendRestrictScalarsAdj φ.hom)).obj P).a ≫
        (ModuleCat.extendRestrictScalarsAdj φ.hom).toComonad.map e.hom =
      e.hom ≫ (toCoalgebra φ N (chartDatum φ P N e)).a := by
  let := φ.hom.toAlgebra
  let := Module.compHom N φ.hom
  let : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change _ = (chartDatum φ P N e).coaction (e.hom x)
  rw [chartDatum, transportDatum_coaction]
  change _ = (((show S ⊗[R] P →ₗ[S] N from e.hom.hom).restrictScalars R).lTensor S)
    ((canonicalDatum P).coaction (e.inv (e.hom x)))
  rw [Iso.hom_inv_id_apply]
  induction x using TensorProduct.inductionOn with
  | tmul s m => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end FLT.Mazur.AffineTensorCocycle

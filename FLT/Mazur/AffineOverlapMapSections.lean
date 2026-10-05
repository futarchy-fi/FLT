/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineOverlapPullback
public import FLT.Mazur.AffineIteratedPullbackSections

/-!
# Naturality of the overlap coefficient charts

Pulling back a sheaf morphism acts on either overlap chart by tensoring
its global-section map. Unit naturality proves the pure-tensor formulas;
additivity extends them to every coefficient.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineOverlapMapSections
open AffineOverlapTensor AffineOverlapPullback AffineIteratedPullbackSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem pullback_map_smul_unit {A B : CommRingCat.{u}} (φ : A ⟶ B)
    {P Q : (Spec A).Modules} (f : P ⟶ Q) (b : B) (n : moduleSpecΓFunctor.obj P) :
    moduleSpecΓFunctor.map ((pullback (Spec.map φ)).map f) (b • specUnit φ P n) =
      b • specUnit φ Q (moduleSpecΓFunctor.map f n) :=
  ((moduleSpecΓFunctor.map ((pullback (Spec.map φ)).map f)).hom.map_smul b _).trans
    (congrArg (b • ·) (specUnit_naturality φ f n))

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (M N : (Spec (.of S)).Modules) [M.IsQuasicoherent] [N.IsQuasicoherent]
attribute [local instance] AffineOverlapPullback.instModuleCarrierCarrierOfCoefficients
local instance (P : (Spec (.of S)).Modules) : IsScalarTower R S (coefficients S P) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
variable (f : M ⟶ N)

/-- The first projection chart tensors the coefficient map on the right. -/
theorem firstSections_map (x : coefficients S M ⊗[R] S) :
    moduleSpecΓFunctor.map ((pullback (Spec.map (CommRingCat.ofHom (left R S)))).map f)
      (firstSections R S M x) =
    firstSections R S N (((moduleSpecΓFunctor.map f).hom.restrictScalars R).rTensor S x) := by
  induction x using TensorProduct.inductionOn with
  | tmul n s =>
    simp only [LinearMap.rTensor_tmul, LinearMap.restrictScalars_apply, firstSections_tmul]
    exact pullback_map_smul_unit (CommRingCat.ofHom (left R S)) f _ n
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The second projection chart tensors the coefficient map on the left. -/
theorem secondSections_map (x : S ⊗[R] coefficients S M) :
    moduleSpecΓFunctor.map ((pullback (Spec.map (CommRingCat.ofHom (right R S)))).map f)
      (secondSections R S M x) =
    secondSections R S N (((moduleSpecΓFunctor.map f).hom.restrictScalars R).lTensor S x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s n =>
    simp only [LinearMap.lTensor_tmul, LinearMap.restrictScalars_apply, secondSections_tmul]
    exact pullback_map_smul_unit (CommRingCat.ofHom (right R S)) f _ n
  | add x y hx hy => simp only [map_add, hx, hy]

end FLT.Mazur.AffineOverlapMapSections

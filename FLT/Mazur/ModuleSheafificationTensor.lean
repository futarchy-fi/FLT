/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModulePresheafTensorHom

/-!
# Sheafification commutes with tensor products

The comparison induced by the two sheafification units is invertible.
Its formula concerns local pure tensors, without any assertion that these
generate all global sections of the tensor sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TensorProduct
open PresheafOfModulesOfCommRing

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace FLT.Mazur.FCurve.ModuleSheafificationTensor

variable {X : Scheme.{u}}

/-- Sheafification over the unchanged structure sheaf. -/
abbrev sheafify : X.PresheafOfModules ⥤ X.Modules :=
  PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)

/-- The sheafification unit as a morphism of module presheaves. -/
abbrev unit (M : X.PresheafOfModules) : M ⟶ (sheafify.obj M).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app M

/-- The canonical tensor comparison, obtained by sheafifying the tensor of units. -/
def comparison (M N : X.PresheafOfModules) :
    sheafify.obj (Monoidal.tensorObj (R := X.presheaf) M N) ⟶
      ModuleSheafTensor.tensor (sheafify.obj M) (sheafify.obj N) :=
  sheafify.map (Monoidal.tensorHom (unit M) (unit N))

instance comparison_isIso (M N : X.PresheafOfModules) : IsIso (comparison M N) := by
  let := ModulePresheafTensorHom.isIso_tensor_unit_left M N
  let := ModulePresheafTensorHom.isIso_tensor_unit_right (sheafify.obj M).val N
  have he : Monoidal.tensorHom (unit M) (unit N) =
      Monoidal.tensorHom (unit M) (𝟙 N) ≫
        Monoidal.tensorHom (𝟙 (sheafify.obj M).val) (unit N) := by
    ext1 U
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    rfl
  dsimp only [comparison]
  rw [he, Functor.map_comp]
  infer_instance

/-- Sheafification of the presheaf tensor is the tensor of the sheafifications. -/
def tensorIso (M N : X.PresheafOfModules) :
    sheafify.obj (Monoidal.tensorObj (R := X.presheaf) M N) ≅
      ModuleSheafTensor.tensor (sheafify.obj M) (sheafify.obj N) :=
  asIso (comparison M N)

/-- The comparison evaluates a local pure tensor by the two sheafification units. -/
lemma comparison_pure (M N : X.PresheafOfModules) (U : X.Opens)
    (m : M.obj (op U)) (n : N.obj (op U)) :
    (comparison M N).app U
      ((unit (Monoidal.tensorObj (R := X.presheaf) M N)).app (op U)
        (m ⊗ₜ[Γ(X, U)] n)) =
      ModuleSheafTensor.pure (sheafify.obj M) (sheafify.obj N) U
        ((unit M).app (op U) m) ((unit N).app (op U) n) := by
  have h := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.naturality (Monoidal.tensorHom (unit M) (unit N))
  exact (congrArg (fun f ↦ f.app (op U) (m ⊗ₜ[Γ(X, U)] n)) h).symm

/-- The sheaf tensor map is the sheafification of the tensor of underlying maps. -/
lemma tensor_map_eq {M N M' N' : X.Modules} (f : M ⟶ M') (g : N ⟶ N') :
    ModuleSheafTensor.map f g = sheafify.map (Monoidal.tensorHom f.val g.val) := by
  apply ModuleSheafTensor.hom_ext
  intro U m n
  rw [ModuleSheafTensor.map_pure]
  have h := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.naturality (Monoidal.tensorHom f.val g.val)
  exact congrArg (fun k ↦ k.app (op U) (m ⊗ₜ[Γ(X, U)] n)) h

/-- Naturality of the canonical comparison in both presheaves. -/
lemma comparison_naturality {M N M' N' : X.PresheafOfModules}
    (f : M ⟶ M') (g : N ⟶ N') :
    sheafify.map (Monoidal.tensorHom f g) ≫ comparison M' N' =
      comparison M N ≫ ModuleSheafTensor.map (sheafify.map f) (sheafify.map g) := by
  rw [tensor_map_eq]
  dsimp only [comparison]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext1 U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  have hf := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.naturality f
  have hg := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.naturality g
  exact congrArg₂ (fun a b ↦ a ⊗ₜ[Γ(X, U.unop)] b)
    (congrArg (fun k ↦ k.app U m) hf) (congrArg (fun k ↦ k.app U n) hg)

end FLT.Mazur.FCurve.ModuleSheafificationTensor

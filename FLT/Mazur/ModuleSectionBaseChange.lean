/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineQuasiCoherentBaseChange

/-!
# The canonical section base-change map

Define the tensor comparison directly from the sheaf pullback unit, for every
scheme morphism. For affine schemes and quasi-coherent modules it is an
isomorphism. Its formula is compatible with sheaf morphisms and restrictions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
open scoped ChangeOfRings
universe u
namespace FLT.Mazur.ModuleSectionBaseChange
open AffineModuleGlobalSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)

/-- Tensor extension of the actual adjunction-unit map on sections over an open. -/
def comparison (U : Y.Opens) :
    (ModuleCat.extendScalars (f.app U).hom).obj (M.val.obj (op U)) ⟶
      ((pullback f).obj M).val.obj (op (f ⁻¹ᵁ U)) :=
  ((ModuleCat.extendRestrictScalarsAdj (f.app U).hom).homEquiv _ _).symm
    (((pullbackPushforwardAdjunction f).unit.app M).val.app (op U))

/-- The canonical comparison sends a unit tensor to the adjunction-unit section. -/
lemma comparison_one_tmul (U : Y.Opens) (m : Γ(M, U)) :
    comparison f M U ((1 : Γ(X, f ⁻¹ᵁ U)) ⊗ₜ[Γ(Y, U),(f.app U).hom] m) =
      ((pullbackPushforwardAdjunction f).unit.app M).app U m := by
  exact congrArg (fun k ↦ k m)
    (((ModuleCat.extendRestrictScalarsAdj (f.app U).hom).homEquiv _ _).apply_symm_apply
      (((pullbackPushforwardAdjunction f).unit.app M).val.app (op U)))

/-- Formula for arbitrary pure tensors in the canonical comparison. -/
lemma comparison_tmul (U : Y.Opens) (s : Γ(X, f ⁻¹ᵁ U)) (m : Γ(M, U)) :
    comparison f M U (s ⊗ₜ[Γ(Y, U),(f.app U).hom] m) =
      s • (show Γ((pullback f).obj M, f ⁻¹ᵁ U) from
        ((pullbackPushforwardAdjunction f).unit.app M).app U m) := by
  have h := (comparison f M U).hom.map_smul s
    (show (ModuleCat.extendScalars (f.app U).hom).obj (M.val.obj (op U)) from
      (1 : Γ(X, f ⁻¹ᵁ U)) ⊗ₜ[Γ(Y, U),(f.app U).hom] m)
  have ht : s • ((1 : Γ(X, f ⁻¹ᵁ U)) ⊗ₜ[Γ(Y, U),(f.app U).hom] m :
      (ModuleCat.extendScalars (f.app U).hom).obj (M.val.obj (op U))) =
      s ⊗ₜ[Γ(Y, U),(f.app U).hom] m := by
    exact (ModuleCat.ExtendScalars.smul_tmul (f.app U).hom s 1 m).trans
      (congrArg (fun a : Γ(X, f ⁻¹ᵁ U) ↦ a ⊗ₜ[Γ(Y, U),(f.app U).hom] m) (mul_one s))
  calc
    _ = s • comparison f M U ((1 : Γ(X, f ⁻¹ᵁ U)) ⊗ₜ[Γ(Y, U),(f.app U).hom] m) :=
      (congrArg (comparison f M U) ht).symm.trans h
    _ = _ := congrArg (fun n : Γ((pullback f).obj M, f ⁻¹ᵁ U) ↦ s • n)
      (comparison_one_tmul f M U m)

/-- On affine schemes the canonical map is the proved section isomorphism. -/
lemma comparison_top_eq [IsAffine X] [IsAffine Y] [M.IsQuasicoherent] :
    comparison f M ⊤ = (AffineQuasiCoherentBaseChange.sectionsIso f M).hom := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  exact (comparison_one_tmul f M ⊤ m).trans
    (AffineQuasiCoherentBaseChange.sectionsIso_unit f M m).symm

/-- Affine quasi-coherent sheaf pullback has the canonical tensor comparison as an iso. -/
instance [IsAffine X] [IsAffine Y] [M.IsQuasicoherent] : IsIso (comparison f M ⊤) := by
  rw [comparison_top_eq]
  infer_instance

/-- The comparison is natural in morphisms of module sheaves. -/
lemma comparison_naturality {N : Y.Modules} (g : M ⟶ N) (U : Y.Opens) :
    (ModuleCat.extendScalars (f.app U).hom).map (g.val.app (op U)) ≫ comparison f N U =
      comparison f M U ≫ ((pullback f).map g).val.app (op (f ⁻¹ᵁ U)) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change comparison f N U
    ((ModuleCat.extendScalars (f.app U).hom).map (g.val.app (op U))
      ((1 : Γ(X, f ⁻¹ᵁ U)) ⊗ₜ[Γ(Y, U),(f.app U).hom] m)) = _
  rw [ModuleCat.ExtendScalars.map_tmul, comparison_one_tmul]
  change _ = ((pullback f).map g).app (f ⁻¹ᵁ U)
    (comparison f M U ((1 : Γ(X, f ⁻¹ᵁ U)) ⊗ₜ[Γ(Y, U),(f.app U).hom] m))
  rw [comparison_one_tmul]
  exact congrArg (fun k ↦ k.app U m) ((pullbackPushforwardAdjunction f).unit.naturality g)

/-- The pure-tensor comparison commutes with actual section restrictions. -/
lemma comparison_restrict {U V : Y.Opens} (i : U ⟶ V)
    (s : Γ(X, f ⁻¹ᵁ V)) (m : Γ(M, V)) :
    ((pullback f).obj M).presheaf.map ((TopologicalSpace.Opens.map f.base).map i).op
      (comparison f M V (s ⊗ₜ[Γ(Y, V),(f.app V).hom] m)) =
    comparison f M U
      ((X.presheaf.map ((TopologicalSpace.Opens.map f.base).map i).op s)
        ⊗ₜ[Γ(Y, U),(f.app U).hom] (M.presheaf.map i.op m)) := by
  rw [comparison_tmul, comparison_tmul, map_smul]
  congr 1
  exact congrArg (fun k ↦ k m)
    (((pullbackPushforwardAdjunction f).unit.app M).mapPresheaf.naturality i.op).symm

end FLT.Mazur.ModuleSectionBaseChange

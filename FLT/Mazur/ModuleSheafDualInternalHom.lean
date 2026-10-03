/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorLineBundleRestrict
public import FLT.Mazur.ModuleSheafTensorCurrying

/-!
# The intrinsic dual and internal Hom

The two sheaves use the same linear subfunctor, indexed respectively by open
subschemes and by slices. Their comparison preserves evaluation and realizes
the actual dual pairing as a morphism out of the sheaf tensor.
-/

open CategoryTheory AlgebraicGeometry Opposite
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
namespace FLT.Mazur.FCurve
variable {X : Scheme.{u}} (M : X.Modules)

/-- The underlying dual and internal Hom presheaves agree through the linear subfunctor. -/
def moduleDualInternalTypesIso :
    (moduleSheafDual M).presheaf ⋙ forget Ab ≅
      (ModuleSheafInternalHom.sheaf M (structureModule X)).presheaf ⋙ forget Ab :=
  (moduleDualTypesIso M).symm ≪≫ ModuleSheafInternalHom.typesIso M (structureModule X)

/-- On a linear local morphism the comparison is its slice-site realization. -/
lemma moduleDualInternalTypesIso_apply (U : X.Opens)
    (φ : (moduleDualLinearHom M).obj (op U)) :
    (moduleDualInternalTypesIso M).hom.app (op U) (moduleDualSectionsEquiv M U φ) =
      moduleDualLinearHomEquiv M U φ := by
  change ModuleSheafInternalHom.sectionsEquiv M (structureModule X) U
    ((moduleDualSectionsEquiv M U).symm (moduleDualSectionsEquiv M U φ)) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- The section comparison preserves addition. -/
lemma moduleDualInternalTypesIso_add (U : X.Opens) (φ ψ : ModuleDualSections M U) :
    (moduleDualInternalTypesIso M).hom.app (op U) (φ + ψ) =
      (moduleDualInternalTypesIso M).hom.app (op U) φ +
        (moduleDualInternalTypesIso M).hom.app (op U) ψ := by
  obtain ⟨φ, rfl⟩ := (moduleDualSectionsEquiv M U).surjective φ
  obtain ⟨ψ, rfl⟩ := (moduleDualSectionsEquiv M U).surjective ψ
  rw [← moduleDualSectionsEquiv_add, moduleDualInternalTypesIso_apply,
    moduleDualInternalTypesIso_apply, moduleDualInternalTypesIso_apply]
  rfl

/-- The comparison of actual module sheaves. -/
def moduleDualInternalHom :
    moduleSheafDual M ⟶ ModuleSheafInternalHom.sheaf M (structureModule X) :=
  ⟨PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun := (moduleDualInternalTypesIso M).hom.app U
          map_zero' := by
            have h := moduleDualInternalTypesIso_add M U.unop 0 0
            simpa only [add_zero, left_eq_add] using h
          map_add' := moduleDualInternalTypesIso_add M U.unop }
      naturality := fun U V g ↦ by
        apply (forget Ab).map_injective
        exact (moduleDualInternalTypesIso M).hom.naturality g }
    (fun U r φ ↦ by
      change (moduleDualInternalTypesIso M).hom.app U (r • φ) =
        ModuleSheafInternalHom.smul M (structureModule X) U.unop r
          ((moduleDualInternalTypesIso M).hom.app U φ)
      obtain ⟨φ, rfl⟩ := (moduleDualSectionsEquiv M U.unop).surjective φ
      rw [← moduleDualSectionsEquiv_smul, moduleDualInternalTypesIso_apply,
        moduleDualInternalTypesIso_apply]
      rfl)⟩

/-- The comparison is invertible on every open. -/
instance moduleDualInternalHom_isIso : IsIso (moduleDualInternalHom M) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ConcreteCategory.bijective_of_isIso ((moduleDualInternalTypesIso M).hom.app (op U))

/-- The intrinsic dual is the internal Hom into the structure module. -/
def moduleSheafDualInternalHomIso :
    moduleSheafDual M ≅ ModuleSheafInternalHom.sheaf M (structureModule X) :=
  asIso (moduleDualInternalHom M)

/-- The comparison preserves the dual pairing on actual sections. -/
lemma moduleDualInternalHom_eval (U : X.Opens) (φ : ModuleDualSections M U)
    (s : Γ(M, U)) :
    ModuleSheafTensorCurrying.eval U ((moduleDualInternalHom M).app U φ) s =
      moduleDualEval M U φ s := rfl

/-- The inverse comparison preserves evaluation as well. -/
lemma moduleSheafDualInternalHomIso_inv_eval (U : X.Opens)
    (φ : ModuleSheafInternalHom.Sections M (structureModule X) U) (s : Γ(M, U)) :
    moduleDualEval M U ((moduleSheafDualInternalHomIso M).inv.app U φ) s =
      ModuleSheafTensorCurrying.eval U φ s := by
  rw [← moduleDualInternalHom_eval]
  have h := congrArg (fun k ↦ k.app U φ) (moduleSheafDualInternalHomIso M).inv_hom_id
  exact congrArg (fun ψ ↦ ModuleSheafTensorCurrying.eval U ψ s) h

/-- The actual evaluation pairing as a morphism from the tensor sheaf. -/
def moduleSheafDualEvaluation :
    ModuleSheafTensor.tensor (moduleSheafDual M) M ⟶ structureModule X :=
  (ModuleSheafTensorCurrying.homEquiv _ _ _).symm (moduleDualInternalHom M)

/-- The tensor pairing evaluates a local dual section on a local module section. -/
lemma moduleSheafDualEvaluation_pure (U : X.Opens) (φ : ModuleDualSections M U)
    (s : Γ(M, U)) :
    (moduleSheafDualEvaluation M).app U
      (ModuleSheafTensor.pure (moduleSheafDual M) M U φ s) = moduleDualEval M U φ s := by
  rw [moduleSheafDualEvaluation, ModuleSheafTensorCurrying.homEquiv_symm_pure,
    moduleDualInternalHom_eval]

/-- Evaluation is natural under precomposition of the dual section. -/
lemma moduleSheafDualEvaluation_naturality {N : X.Modules} (f : M ⟶ N) :
    ModuleSheafTensor.map (moduleSheafDualMap M f) (𝟙 M) ≫ moduleSheafDualEvaluation M =
      ModuleSheafTensor.map (𝟙 (moduleSheafDual N)) f ≫ moduleSheafDualEvaluation N := by
  apply ModuleSheafTensor.hom_ext
  intro U φ s
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    ModuleSheafTensor.map_pure, Scheme.Modules.Hom.id_app, ConcreteCategory.id_apply,
    moduleSheafDualEvaluation_pure, moduleSheafDualMap_app]
  exact moduleDualEval_precomp f U φ s

end FLT.Mazur.FCurve

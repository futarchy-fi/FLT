/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Module structures on specified additive sheaves

Transport a sheaf module structure through an additive sheaf isomorphism.
The construction retains the given additive sections and restriction maps,
and the original comparison becomes an isomorphism of sheaves of modules.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory

universe u v w r

namespace FLT.Mazur.AdditiveSheafModuleTransport

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{r}} (A : Sheaf J AddCommGrpCat.{w})
variable (M : SheafOfModules.{w} R) (e : A ≅ (SheafOfModules.toSheaf R).obj M)

/-- The additive comparison on sections, with its module-valued target explicit. -/
def sectionEquiv (U : Cᵒᵖ) : A.obj.obj U ≃+ M.val.obj U where
  toFun := e.hom.hom.app U
  invFun := e.inv.hom.app U
  left_inv := (((sheafToPresheaf J AddCommGrpCat).mapIso e).app U).hom_inv_id_apply
  right_inv := (((sheafToPresheaf J AddCommGrpCat).mapIso e).app U).inv_hom_id_apply
  map_add' := (e.hom.hom.app U).hom.map_add

/-- The comparison commutes with the unchanged restriction maps. -/
lemma map_restrict {U V : Cᵒᵖ} (i : U ⟶ V) (s : A.obj.obj U) :
    sectionEquiv A M e V (A.obj.map i s) = M.val.map i (sectionEquiv A M e U s) :=
  ConcreteCategory.congr_hom (e.hom.hom.naturality i) s

/-- The transported module structure keeps the original additive group. -/
@[instance_reducible]
def sectionModule (U : Cᵒᵖ) : Module (R.obj.obj U) (A.obj.obj U) :=
  (sectionEquiv A M e U).module (R.obj.obj U)

/-- The original section comparison is linear for the transported action. -/
def sectionLinearEquiv (U : Cᵒᵖ) :
    let := sectionModule A M e U
    A.obj.obj U ≃ₗ[R.obj.obj U] M.val.obj U :=
  (sectionEquiv A M e U).linearEquiv (R.obj.obj U)

/-- Recovery sends the transported scalar action to the original action. -/
lemma map_smul (U : Cᵒᵖ) (r : R.obj.obj U) (s : A.obj.obj U) :
    let := sectionModule A M e U
    sectionEquiv A M e U (r • s) = r • sectionEquiv A M e U s :=
  (sectionLinearEquiv A M e U).map_smul r s

/-- The given restriction maps are semilinear for the transported action. -/
lemma restrict_smul {U V : Cᵒᵖ} (i : U ⟶ V) (r : R.obj.obj U) (s : A.obj.obj U) :
    let := sectionModule A M e U
    let := sectionModule A M e V
    A.obj.map i (r • s) = R.obj.map i r • A.obj.map i s := by
  intro _ _
  apply (sectionEquiv A M e V).injective
  rw [map_restrict, map_smul, map_smul, map_restrict, M.val.map_smul]

/-- The module sheaf on the given additive sheaf, with its original restrictions. -/
def moduleSheaf : SheafOfModules.{w} R := by
  let (U : Cᵒᵖ) := sectionModule A M e U
  exact {
    val := PresheafOfModules.ofPresheaf A.obj (fun _ _ i r s ↦ restrict_smul A M e i r s)
    isSheaf := A.property }

/-- Forgetting the transported action recovers the specified additive sheaf exactly. -/
lemma moduleSheaf_underlying :
    (SheafOfModules.toSheaf R).obj (moduleSheaf A M e) = A := rfl

/-- The given additive comparison upgraded to a module sheaf isomorphism. -/
def moduleIso : moduleSheaf A M e ≅ M :=
  (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk
      (fun U ↦ (sectionLinearEquiv A M e U).toModuleIso) (by
        intro U V i
        ext s
        exact map_restrict A M e i s))

/-- The linear comparison retains the original additive comparison. -/
lemma moduleIso_underlying :
    (SheafOfModules.toSheaf R).map (moduleIso A M e).hom = e.hom := rfl

end FLT.Mazur.AdditiveSheafModuleTransport

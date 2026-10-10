/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineTensorEquivalence
public import FLT.Mazur.ModuleGlobalUnitGenerator

/-!
# Sections of a tensor twist as morphisms from the dual line

Full faithfulness of the concrete tensor functor identifies a section of
`L tensor B` with a morphism from the intrinsic dual of `B` to `L`.
The normalization uses the actual evaluation, not a chosen trivialization.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open ModuleSheafTensor
variable {X : Scheme.{u}}

/-- Global sections are exactly morphisms from the structure module. -/
def globalSectionHomEquiv (M : X.Modules) : Γ(M, ⊤) ≃ (structureModule X ⟶ M) where
  toFun := globalSectionHom M
  invFun a := a.app ⊤ (1 : Γ(X, ⊤))
  left_inv := globalSectionHom_top M
  right_inv _ :=  globalSection_hom_ext _ _ (globalSectionHom_top M _)

/-- A dual-line morphism gives a section by tensoring and inverse evaluation. -/
def lineHomSectionEquiv (L : X.Modules) {B : X.Modules} (hB : LocallyFreeRankOne B) :
    (moduleSheafDual B ⟶ L) ≃ Γ(tensor L B, ⊤) :=
  (lineTensorEquivalence hB).fullyFaithfulFunctor.homEquiv.trans
    ((Iso.homCongr (lineSheafDualEvaluationIso hB) (Iso.refl (tensor L B))).trans
      (globalSectionHomEquiv (tensor L B)).symm)

/-- The resulting section is normalized by the intrinsic dual evaluation. -/
lemma lineHomSectionEquiv_hom (L : X.Modules) {B : X.Modules}
    (hB : LocallyFreeRankOne B) (a : moduleSheafDual B ⟶ L) :
    globalSectionHom (tensor L B) (lineHomSectionEquiv L hB a) =
      (lineSheafDualEvaluationIso hB).inv ≫ map a (𝟙 B) := by
  apply globalSection_hom_ext
  rw [globalSectionHom_top]
  rfl

/-- Tensoring the recovered morphism recovers the original section map. -/
lemma lineHomSectionEquiv_symm_tensor (L : X.Modules) {B : X.Modules}
    (hB : LocallyFreeRankOne B) (s : Γ(tensor L B, ⊤)) :
    map ((lineHomSectionEquiv L hB).symm s) (𝟙 B) =
      (lineSheafDualEvaluationIso hB).hom ≫ globalSectionHom (tensor L B) s := by
  rw [← (lineHomSectionEquiv L hB).apply_symm_apply s, lineHomSectionEquiv_hom]
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp,
    Equiv.symm_apply_apply]

/-- Transporting the target sheaf postcomposes the corresponding dual-line morphism. -/
lemma lineHomSectionEquiv_naturality {L P B : X.Modules} (hB : LocallyFreeRankOne B)
    (a : moduleSheafDual B ⟶ L) (b : L ⟶ P) :
    lineHomSectionEquiv P hB (a ≫ b) =
      (map b (𝟙 B)).app ⊤ (lineHomSectionEquiv L hB a) := by
  apply (globalSectionHomEquiv (tensor P B)).injective
  change globalSectionHom _ _ = globalSectionHom _ _
  rw [← globalSectionHom_naturality, lineHomSectionEquiv_hom, lineHomSectionEquiv_hom]
  rw [show map (a ≫ b) (𝟙 B) = map a (𝟙 B) ≫ map b (𝟙 B) by
    simpa only [Category.id_comp] using ModuleSheafTensor.map_comp a b (𝟙 B) (𝟙 B)]
  exact (Category.assoc _ _ _).symm

end FLT.Mazur.FCurve

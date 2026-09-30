/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModulePresheafPullbackSections
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Limits.Colimits
public import Mathlib.CategoryTheory.Filtered.Final

/-!
# Tensor products and presheaf pullback

Scalar extension commutes with tensor products. The section diagrams from
`ModulePresheafPullbackSections` are filtered, so tensoring their colimit cocones
again gives a colimit. These comparisons assemble into an isomorphism of module
presheaves, natural in both inputs and with an explicit formula on generators.
-/

open CategoryTheory AlgebraicGeometry Opposite Limits MonoidalCategory
open scoped ChangeOfRings
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
namespace FLT.Mazur.FCurve.ModulePresheafTensorPullback
open ModulePresheafPullbackSections
attribute [local instance] IsFiltered.isSifted
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (V : X.Opens)
  (M N : Y.PresheafOfModules)
/-- The sectionwise tensor of module presheaves. -/
abbrev tensor := PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := Y.presheaf) M N

/-- Scalar extension distributes over the tensor on one indexing open. -/
def termIso (U : Index f V) :
    term f V (tensor M N) U ≅ term f V M U ⊗ term f V N U := by
  letI := (scalar f V U).toAlgebra
  exact (TensorProduct.AlgebraTensorModule.distribBaseChange
    Γ(Y, U.val) Γ(X, V) (M.obj (op U.val)) (N.obj (op U.val))).toModuleIso

/-- The scalar-extension comparison on pure tensors. -/
lemma termIso_tmul (U : Index f V) (r : Γ(X, V))
    (m : M.obj (op U.val)) (n : N.obj (op U.val)) :
    (termIso f V M N U).hom (r ⊗ₜ[Γ(Y, U.val), scalar f V U] (m ⊗ₜ[Γ(Y, U.val)] n)) =
      (r ⊗ₜ[Γ(Y, U.val), scalar f V U] m) ⊗ₜ[Γ(X, V)]
        ((1 : Γ(X, V)) ⊗ₜ[Γ(Y, U.val), scalar f V U] n) := rfl

/-- The scalar-extension tensor comparisons form an isomorphism of diagrams. -/
def diagramIso : diagram f V (tensor M N) ≅ diagram f V M ⊗ diagram f V N :=
  NatIso.ofComponents (fun U => termIso f V M N U.unop) (fun {U W} i => by
    apply ModuleCat.ExtendScalars.hom_ext
    intro t
    induction t using TensorProduct.inductionOn with
    | add t s ht hs => simp only [TensorProduct.tmul_add, map_add, ht, hs]
    | tmul m n =>
      simp only [ModuleCat.comp_apply]
      change (termIso f V M N W.unop).hom (transition f V (tensor M N) i.unop _) =
        (transition f V M i.unop ⊗ₘ transition f V N i.unop)
          ((termIso f V M N U.unop).hom _)
      rw [transition_one, termIso_tmul]
      erw [termIso_tmul]
      change _ = transition f V M i.unop _ ⊗ₜ[Γ(X, V)] transition f V N i.unop _
      rw [transition_one, transition_one]
      rfl)

/-- The tensor of the two section cocones, transported along scalar extension. -/
def tensorCocone : Cocone (diagram f V (tensor M N)) :=
  (Cocone.precompose (diagramIso f V M N).hom).obj
    ((cocone f V M).tensor (cocone f V N))

/-- Filteredness makes the tensor cocone colimiting. -/
def tensorIsColimit : IsColimit (tensorCocone f V M N) :=
  (IsColimit.precomposeHomEquiv (diagramIso f V M N) _).symm
    ((isColimit f V M).tensor (isColimit f V N))

/-- Pullback commutes with tensor product on sections of a fixed open. -/
def sectionsIso : (pull f (tensor M N)).obj (op V) ≅
    (pull f M).obj (op V) ⊗ (pull f N).obj (op V) :=
  (isColimit f V (tensor M N)).coconePointUniqueUpToIso (tensorIsColimit f V M N)
/-- The section comparison respects the structure maps of the colimit. -/
lemma component_sectionsIso (U : Index f V) :
    component f V (tensor M N) U ≫ (sectionsIso f V M N).hom =
      (termIso f V M N U).hom ≫ (component f V M U ⊗ₘ component f V N U) :=
  (isColimit f V (tensor M N)).comp_coconePointUniqueUpToIso_hom
    (tensorIsColimit f V M N) (op U)

/-- The section comparison sends a pure generator to the tensor of its images. -/
lemma sectionsIso_generator (U : Index f V) (r : Γ(X, V))
    (m : M.obj (op U.val)) (n : N.obj (op U.val)) :
    (sectionsIso f V M N).hom (component f V (tensor M N) U
      (r ⊗ₜ[Γ(Y, U.val), scalar f V U] (m ⊗ₜ[Γ(Y, U.val)] n))) =
      component f V M U (r ⊗ₜ[Γ(Y, U.val), scalar f V U] m) ⊗ₜ[Γ(X, V)]
        component f V N U ((1 : Γ(X, V)) ⊗ₜ[Γ(Y, U.val), scalar f V U] n) := by
  erw [← ModuleCat.comp_apply, component_sectionsIso, ModuleCat.comp_apply, termIso_tmul]
  rfl

/-- Pullback commutes with the tensor of module presheaves. -/
def pullbackTensorIso : pull f (tensor M N) ≅ tensor (pull f M) (pull f N) :=
  PresheafOfModulesOfCommRing.isoMk (fun V => sectionsIso f V.unop M N) (fun {V W} i => by
    apply (isColimit f V.unop (tensor M N)).hom_ext
    intro U
    apply ModuleCat.ExtendScalars.hom_ext
    intro t
    induction t using TensorProduct.inductionOn with
    | add t s ht hs => simp only [TensorProduct.tmul_add, map_add, ht, hs]
    | tmul m n =>
      change (sectionsIso f W.unop M N).hom ((pull f (tensor M N)).map i
          (component f V.unop (tensor M N) U.unop _)) =
        (tensor (pull f M) (pull f N)).map i
          ((sectionsIso f V.unop M N).hom (component f V.unop (tensor M N) U.unop _))
      erw [component_restrict f V.unop (tensor M N) i.unop,
        sectionsIso_generator, sectionsIso_generator]
      erw [PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul]
      erw [component_restrict f V.unop M i.unop,
        component_restrict f V.unop N i.unop]
      rw [map_one])

/-- The presheaf isomorphism on the scalar-extended section generators. -/
lemma pullbackTensorIso_generator (V : X.Opens) (U : Index f V) (r : Γ(X, V))
    (m : M.obj (op U.val)) (n : N.obj (op U.val)) :
    (pullbackTensorIso f M N).hom.app (op V) (component f V (tensor M N) U
      (r ⊗ₜ[Γ(Y, U.val), scalar f V U] (m ⊗ₜ[Γ(Y, U.val)] n))) =
      component f V M U (r ⊗ₜ[Γ(Y, U.val), scalar f V U] m) ⊗ₜ[Γ(X, V)]
        component f V N U ((1 : Γ(X, V)) ⊗ₜ[Γ(Y, U.val), scalar f V U] n) :=
  sectionsIso_generator f V M N U r m n

/-- The pullback/tensor comparison is natural in both presheaves. -/
lemma pullbackTensorIso_naturality {M' N' : Y.PresheafOfModules}
    (α : M ⟶ M') (β : N ⟶ N') :
    (PresheafOfModules.pullback f.toRingCatSheafHom.hom).map
        (PresheafOfModulesOfCommRing.Monoidal.tensorHom α β) ≫
      (pullbackTensorIso f M' N').hom =
    (pullbackTensorIso f M N).hom ≫ PresheafOfModulesOfCommRing.Monoidal.tensorHom
      ((PresheafOfModules.pullback f.toRingCatSheafHom.hom).map α)
      ((PresheafOfModules.pullback f.toRingCatSheafHom.hom).map β) := by
  ext1 V
  apply (isColimit f V.unop (tensor M N)).hom_ext
  intro U
  apply ModuleCat.ExtendScalars.hom_ext
  intro t
  induction t using TensorProduct.inductionOn with
  | add t s ht hs => simp only [TensorProduct.tmul_add, map_add, ht, hs]
  | tmul m n =>
    change (pullbackTensorIso f M' N').hom.app V
        (((PresheafOfModules.pullback f.toRingCatSheafHom.hom).map
          (PresheafOfModulesOfCommRing.Monoidal.tensorHom α β)).app V
          (component f V.unop (tensor M N) U.unop _)) = _
    rw [component_map]
    erw [pullbackTensorIso_generator]
    change _ = (PresheafOfModulesOfCommRing.Monoidal.tensorHom
      ((PresheafOfModules.pullback f.toRingCatSheafHom.hom).map α)
      ((PresheafOfModules.pullback f.toRingCatSheafHom.hom).map β)).app V
        ((pullbackTensorIso f M N).hom.app V
          (component f V.unop (tensor M N) U.unop _))
    erw [pullbackTensorIso_generator]
    change _ = ((PresheafOfModules.pullback f.toRingCatSheafHom.hom).map α).app V _
      ⊗ₜ[Γ(X, V.unop)]
        ((PresheafOfModules.pullback f.toRingCatSheafHom.hom).map β).app V _
    rw [component_map, component_map]
    rfl

end FLT.Mazur.FCurve.ModulePresheafTensorPullback

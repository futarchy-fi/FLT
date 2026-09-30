/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleLineBundlePullback
public import FLT.Mazur.ModulePresheafTensorPullback
public import FLT.Mazur.ModuleSheafificationTensor

/-!
# Tensor products and powers under arbitrary pullback

The presheaf tensor comparison and tensor compatibility of sheafification
give the comparison for actual module sheaves. Tensor powers include the
structure module in degree zero.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TensorProduct

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace FLT.Mazur.FCurve.ModuleLineBundleTensorPullback

open ModuleSheafTensor (tensor)
open ModuleSheafificationTensor (sheafify)

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The chosen sheaf pullback as sheafification of the presheaf pullback. -/
abbrev pullbackIso (M : Y.Modules) :
    (Scheme.Modules.pullback f).obj M ≅
      sheafify.obj ((PresheafOfModules.pullback f.toRingCatSheafHom.hom).obj M.val) :=
  (SheafOfModules.pullbackIso f.toRingCatSheafHom).app M

/-- Pullback commutes with the actual tensor of module sheaves. -/
def tensorIso (M N : Y.Modules) :
    (Scheme.Modules.pullback f).obj (tensor M N) ≅
      tensor ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) :=
  (SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom).app
      (ModuleSheafTensor.tensorPresheaf M N) ≪≫
    sheafify.mapIso (ModulePresheafTensorPullback.pullbackTensorIso f M.val N.val) ≪≫
    ModuleSheafificationTensor.tensorIso _ _ ≪≫
    ModuleSheafTensor.congr (pullbackIso f M).symm (pullbackIso f N).symm

/-- The tensor comparison is natural in both sheaves. -/
lemma tensorIso_naturality {M N M' N' : Y.Modules} (a : M ⟶ M') (b : N ⟶ N') :
    (Scheme.Modules.pullback f).map (ModuleSheafTensor.map a b) ≫
      (tensorIso f M' N').hom =
    (tensorIso f M N).hom ≫ ModuleSheafTensor.map
      ((Scheme.Modules.pullback f).map a) ((Scheme.Modules.pullback f).map b) := by
  let F := PresheafOfModules.pullback f.toRingCatSheafHom.hom
  let C := SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom
  have h₁ := C.hom.naturality
    (PresheafOfModulesOfCommRing.Monoidal.tensorHom a.val b.val)
  have h₂ := congrArg sheafify.map
    (ModulePresheafTensorPullback.pullbackTensorIso_naturality f M.val N.val a.val b.val)
  have h₃ := ModuleSheafificationTensor.comparison_naturality (F.map a.val) (F.map b.val)
  have h₄ := (SheafOfModules.pullbackIso f.toRingCatSheafHom).inv.naturality a
  have h₅ := (SheafOfModules.pullbackIso f.toRingCatSheafHom).inv.naturality b
  dsimp only [tensorIso, Iso.trans_hom, ModuleSheafTensor.congr, Iso.symm_hom]
  rw [ModuleSheafificationTensor.tensor_map_eq]
  change _ ≫ (C.hom.app _ ≫ _) = _
  erw [← Category.assoc, h₁]
  simp only [Category.assoc]
  congr 1
  simp only [Functor.map_comp] at h₂
  erw [← Category.assoc, h₂]
  simp only [Category.assoc]
  congr 1
  erw [← Category.assoc, h₃]
  simp only [Category.assoc]
  congr 1
  change ModuleSheafTensor.map (sheafify.map (F.map a.val))
      (sheafify.map (F.map b.val)) ≫
    ModuleSheafTensor.map (pullbackIso f M').inv (pullbackIso f N').inv =
      ModuleSheafTensor.map (pullbackIso f M).inv (pullbackIso f N).inv ≫
        ModuleSheafTensor.map ((Scheme.Modules.pullback f).map a)
          ((Scheme.Modules.pullback f).map b)
  rw [← ModuleSheafTensor.map_comp, ← ModuleSheafTensor.map_comp]
  exact congrArg₂ ModuleSheafTensor.map h₄ h₅

/-- The pullback comparison identifies the two adjunction-unit sections. -/
lemma pullbackIso_unit (M : Y.Modules) (U : Y.Opens) (m : Γ(M, U)) :
    (pullbackIso f M).hom.app (f ⁻¹ᵁ U)
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U m) =
    (ModuleSheafificationTensor.unit
      ((PresheafOfModules.pullback f.toRingCatSheafHom.hom).obj M.val)).app (op (f ⁻¹ᵁ U))
        (((PresheafOfModules.pullbackPushforwardAdjunction
          f.toRingCatSheafHom.hom).unit.app M.val).app (op U) m) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom)
    (SheafOfModules.PullbackConstruction.adjunction f.toRingCatSheafHom) M
  exact congrArg (fun k ↦ k.val.app (op U) m) h

/-- The inverse comparison carries a sheafified presheaf-unit section to the sheaf unit. -/
lemma pullbackIso_inv_unit (M : Y.Modules) (U : Y.Opens) (m : Γ(M, U)) :
    (pullbackIso f M).inv.app (f ⁻¹ᵁ U)
      ((ModuleSheafificationTensor.unit
        ((PresheafOfModules.pullback f.toRingCatSheafHom.hom).obj M.val)).app
          (op (f ⁻¹ᵁ U)) (((PresheafOfModules.pullbackPushforwardAdjunction
            f.toRingCatSheafHom.hom).unit.app M.val).app (op U) m)) =
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U m) := by
  rw [← pullbackIso_unit]
  exact congrArg (fun k ↦ k.app (f ⁻¹ᵁ U)
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U m))
      (pullbackIso f M).hom_inv_id

/-- On adjunction-unit sections, the presheaf comparison is the pure-tensor map. -/
lemma presheafTensorIso_unit (M N : Y.Modules) (U : Y.Opens)
    (m : Γ(M, U)) (n : Γ(N, U)) :
    (ModulePresheafTensorPullback.pullbackTensorIso f M.val N.val).hom.app (op (f ⁻¹ᵁ U))
      (((PresheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom.hom).unit.app
        (ModuleSheafTensor.tensorPresheaf M N)).app (op U) (m ⊗ₜ[Γ(Y, U)] n)) =
    (show ((PresheafOfModules.pullback f.toRingCatSheafHom.hom).obj M.val).obj
      (op (f ⁻¹ᵁ U)) from
      (((PresheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom.hom).unit.app
        M.val).app (op U) m)) ⊗ₜ[Γ(X, f ⁻¹ᵁ U)]
      (show ((PresheafOfModules.pullback f.toRingCatSheafHom.hom).obj N.val).obj
        (op (f ⁻¹ᵁ U)) from
        (((PresheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom.hom).unit.app
          N.val).app (op U) n)) := by
  have h := ModulePresheafTensorPullback.pullbackTensorIso_generator
    f M.val N.val (f ⁻¹ᵁ U) ⟨U, le_rfl⟩ 1 m n
  erw [ModulePresheafPullbackSections.component_one,
    ModulePresheafPullbackSections.component_one,
    ModulePresheafPullbackSections.component_one] at h
  have hi (A : X.PresheafOfModules) (V : X.Opens) (a : A.obj (op V)) :
      A.map (𝟙 (op V)) a = a := by
    change A.presheaf.map (𝟙 _) a = a
    simp
  erw [hi, hi, hi] at h
  exact h

/-- Sheafification maps commute with their canonical unit sections. -/
lemma sheafify_map_unit {A B : X.PresheafOfModules} (a : A ⟶ B)
    (U : X.Opens) (s : A.obj (op U)) :
    (sheafify.map a).app U ((ModuleSheafificationTensor.unit A).app (op U) s) =
      (ModuleSheafificationTensor.unit B).app (op U) (a.app (op U) s) :=
  (congrArg (fun k ↦ k.app (op U) s)
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.naturality a)).symm

set_option maxHeartbeats 600000 in
-- Evaluating the comparison unfolds both chosen adjunctions and scalar restrictions.
/-- Transposing the tensor comparison gives the tensor of the two pullback units. -/
lemma tensorIso_adj_pure (M N : Y.Modules) (U : Y.Opens) (m : Γ(M, U)) (n : Γ(N, U)) :
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      (tensorIso f M N).hom).app U (ModuleSheafTensor.pure M N U m n) =
    ModuleSheafTensor.pure _ _ (f ⁻¹ᵁ U)
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U m)
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).app U n) := by
  let A := PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)
  let B := SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom
  let C := PresheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom.hom
  let D := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let K := sheafify.mapIso
      (ModulePresheafTensorPullback.pullbackTensorIso f M.val N.val) ≪≫
    ModuleSheafificationTensor.tensorIso _ _ ≪≫
    ModuleSheafTensor.congr (pullbackIso f M).symm (pullbackIso f N).symm
  have he : (A.comp B).homEquiv _ _ (tensorIso f M N).hom =
      (C.comp D).homEquiv _ _ K.hom := by
    change (A.comp B).homEquiv _ _
      (((A.comp B).leftAdjointUniq (C.comp D)).hom.app _ ≫ K.hom) = _
    rw [Adjunction.homEquiv_naturality_right,
      Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit]
    rfl
  have h := congrArg (fun k ↦ k.app (op U) (m ⊗ₜ[Γ(Y, U)] n)) he
  change ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
    (tensorIso f M N).hom).app U (ModuleSheafTensor.pure M N U m n) =
      K.hom.app (f ⁻¹ᵁ U)
    ((ModuleSheafificationTensor.unit _).app (op (f ⁻¹ᵁ U))
      ((C.unit.app (ModuleSheafTensor.tensorPresheaf M N)).app (op U)
        (m ⊗ₜ[Γ(Y, U)] n))) at h
  dsimp only [K, Iso.trans_hom, Functor.mapIso_hom, ModuleSheafTensor.congr,
    Iso.symm_hom, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    ModuleSheafificationTensor.tensorIso, asIso_hom] at h
  simp only [ConcreteCategory.comp_apply] at h
  have hs := sheafify_map_unit
    (ModulePresheafTensorPullback.pullbackTensorIso f M.val N.val).hom (f ⁻¹ᵁ U)
      ((C.unit.app (ModuleSheafTensor.tensorPresheaf M N)).app (op U)
        (m ⊗ₜ[Γ(Y, U)] n))
  conv_rhs at h => erw [hs]
  conv_rhs at h => erw [presheafTensorIso_unit f M N U m n]
  have hc := ModuleSheafificationTensor.comparison_pure
    ((PresheafOfModules.pullback f.toRingCatSheafHom.hom).obj M.val)
    ((PresheafOfModules.pullback f.toRingCatSheafHom.hom).obj N.val) (f ⁻¹ᵁ U)
    ((C.unit.app M.val).app (op U) m) ((C.unit.app N.val).app (op U) n)
  conv_rhs at h => erw [hc]
  conv_rhs at h =>
    erw [ModuleSheafTensor.map_pure (pullbackIso f M).inv (pullbackIso f N).inv]
  conv_rhs at h => erw [pullbackIso_inv_unit f M U m, pullbackIso_inv_unit f N U n]
  exact h

set_option maxHeartbeats 600000 in
-- The unit diagram compares chosen pullbacks through their adjunction equivalences.
/-- Compatibility with the canonical structure-module comparison and left unitors. -/
lemma tensorIso_leftUnitor (M : Y.Modules) :
    (tensorIso f (structureModule Y) M).hom ≫
      ModuleSheafTensor.map (modulePullbackUnitIso f).hom (𝟙 _) ≫
        (ModuleSheafTensor.leftUnitor ((Scheme.Modules.pullback f).obj M)).hom =
      (Scheme.Modules.pullback f).map (ModuleSheafTensor.leftUnitor M).hom := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  apply (adj.homEquiv _ _).injective
  apply ModuleSheafTensor.hom_ext
  intro U r m
  have ht : adj.homEquiv _ _
      ((Scheme.Modules.pullback f).map (ModuleSheafTensor.leftUnitor M).hom) =
      (ModuleSheafTensor.leftUnitor M).hom ≫ adj.unit.app M := by
    simpa only [Category.comp_id, Adjunction.homEquiv_id] using
      adj.homEquiv_naturality_left (ModuleSheafTensor.leftUnitor M).hom (𝟙 _)
  erw [Adjunction.homEquiv_naturality_right, ht]
  change _ = ((ModuleSheafTensor.leftUnitor M).hom ≫ adj.unit.app M).app U
    (ModuleSheafTensor.pure (structureModule Y) M U r m)
  simp only [Scheme.Modules.pushforward_map_app, Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply]
  erw [tensorIso_adj_pure f (structureModule Y) M U r m]
  let r' : Γ((Scheme.Modules.pullback f).obj (structureModule Y), f ⁻¹ᵁ U) :=
    ((adj.unit.app (structureModule Y)).app U r)
  let m' : Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ U) := (adj.unit.app M).app U m
  have hmap := ModuleSheafTensor.map_pure (X := X) (modulePullbackUnitIso f).hom
    (𝟙 ((Scheme.Modules.pullback f).obj M)) (f ⁻¹ᵁ U) r' m'
  erw [hmap]
  erw [ModuleSheafTensor.leftUnitor_pure (X := X) ((Scheme.Modules.pullback f).obj M)
    (f ⁻¹ᵁ U) ((modulePullbackUnitIso f).hom.app (f ⁻¹ᵁ U) r') m',
    ModuleSheafTensor.leftUnitor_pure (X := Y) M U r m]
  have h := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    f.toRingCatSheafHom
  have hr := congrArg (fun k ↦ k.val.app (op U) r) h
  change (modulePullbackUnitIso f).hom.app (f ⁻¹ᵁ U)
    ((adj.unit.app (structureModule Y)).app U r) = f.app U r at hr
  erw [hr, Scheme.Modules.Hom.app_smul]
  rfl

/-- Tensor powers of a module sheaf, with the structure module in degree zero. -/
def tensorPower (M : X.Modules) : ℕ → X.Modules
  | 0 => structureModule X
  | n + 1 => tensor M (tensorPower M n)

/-- Pullback commutes with every natural tensor power. -/
def tensorPowerIso (M : Y.Modules) : ∀ n : ℕ,
    (Scheme.Modules.pullback f).obj (tensorPower M n) ≅
      tensorPower ((Scheme.Modules.pullback f).obj M) n
  | 0 => modulePullbackUnitIso f
  | n + 1 => tensorIso f M (tensorPower M n) ≪≫
      ModuleSheafTensor.congr (Iso.refl _) (tensorPowerIso M n)

/-- The degree-zero comparison is the canonical structure-module comparison. -/
@[simp]
lemma tensorPowerIso_zero (M : Y.Modules) :
    tensorPowerIso f M 0 = modulePullbackUnitIso f := rfl

/-- The successor comparison tensors the previous power comparison. -/
@[simp]
lemma tensorPowerIso_succ (M : Y.Modules) (n : ℕ) :
    tensorPowerIso f M (n + 1) = tensorIso f M (tensorPower M n) ≪≫
      ModuleSheafTensor.congr (Iso.refl _) (tensorPowerIso f M n) := rfl

end FLT.Mazur.FCurve.ModuleLineBundleTensorPullback

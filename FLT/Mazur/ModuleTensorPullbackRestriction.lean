/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleLineBundleTensorPullback
public import FLT.Mazur.ModulePullbackRestrictionPasting
public import FLT.Mazur.ModuleSheafTensorRestrict

/-!
# Tensor pullback and open restriction

The tensor comparison respects composition and the chosen open-immersion
comparisons. Pasting these identities proves its compatibility with a
commuting square of open immersions. The proofs test actual adjunction-unit
sections, so the result applies to the canonical evaluation pairing.
-/

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
namespace FLT.Mazur.FCurve.ModuleLineBundleTensorPullback
variable {X Y Z : Scheme.{u}}
/-- The inverse composition comparison preserves the tensor comparison. -/
lemma tensorIso_comp_inv (f : X ⟶ Y) (g : Y ⟶ Z) (M N : Z.Modules) :
    (pullbackComp f g).inv.app (ModuleSheafTensor.tensor M N) ≫
      (pullback f).map (tensorIso g M N).hom ≫
      (tensorIso f ((pullback g).obj M) ((pullback g).obj N)).hom =
    (tensorIso (f ≫ g) M N).hom ≫ ModuleSheafTensor.map
      ((pullbackComp f g).inv.app M) ((pullbackComp f g).inv.app N) := by
  apply ((pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _).injective
  apply ModuleSheafTensor.hom_ext
  intro U m n
  change (tensorIso f _ _).hom.app _
    (((pullback f).map (tensorIso g M N).hom).app _
      (((pullbackComp f g).inv.app _).app _
        (((pullbackPushforwardAdjunction (f ≫ g)).unit.app _).app U
          (ModuleSheafTensor.pure M N U m n)))) =
    (ModuleSheafTensor.map ((pullbackComp f g).inv.app M)
      ((pullbackComp f g).inv.app N)).app _
      ((tensorIso (f ≫ g) M N).hom.app _
        (((pullbackPushforwardAdjunction (f ≫ g)).unit.app _).app U
          (ModuleSheafTensor.pure M N U m n)))
  have hc := tensorIso_adj_pure (f ≫ g) M N U m n
  change (tensorIso (f ≫ g) M N).hom.app _
    (((pullbackPushforwardAdjunction (f ≫ g)).unit.app _).app U _) = _ at hc
  rw [hc, ModuleSheafTensor.map_pure]
  rw [modulePullbackComp_inv_unit, modulePullbackComp_inv_unit,
    modulePullbackComp_inv_unit]
  have hn := congrArg (fun k ↦ k.app (g ⁻¹ᵁ U)
    (((pullbackPushforwardAdjunction g).unit.app _).app U
      (ModuleSheafTensor.pure M N U m n)))
    ((pullbackPushforwardAdjunction f).unit.naturality (tensorIso g M N).hom).symm
  change ((pullback f).map (tensorIso g M N).hom).app _
    (((pullbackPushforwardAdjunction f).unit.app _).app _ _) =
    ((pullbackPushforwardAdjunction f).unit.app _).app _
      ((tensorIso g M N).hom.app _ _) at hn
  erw [hn]
  have hg := tensorIso_adj_pure g M N U m n
  change (tensorIso g M N).hom.app _
    (((pullbackPushforwardAdjunction g).unit.app _).app U _) = _ at hg
  erw [hg]
  exact tensorIso_adj_pure f ((pullback g).obj M) ((pullback g).obj N) (g ⁻¹ᵁ U)
    (((pullbackPushforwardAdjunction g).unit.app M).app U m)
    (((pullbackPushforwardAdjunction g).unit.app N).app U n)
/-- The composition comparison preserves the tensor comparison. -/
lemma tensorIso_comp_hom (f : X ⟶ Y) (g : Y ⟶ Z) (M N : Z.Modules) :
    (pullbackComp f g).hom.app (ModuleSheafTensor.tensor M N) ≫
      (tensorIso (f ≫ g) M N).hom =
    (pullback f).map (tensorIso g M N).hom ≫
      (tensorIso f ((pullback g).obj M) ((pullback g).obj N)).hom ≫
      ModuleSheafTensor.map ((pullbackComp f g).hom.app M)
        ((pullbackComp f g).hom.app N) := by
  rw [← cancel_epi ((pullbackComp f g).inv.app (ModuleSheafTensor.tensor M N))]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% tensorIso_comp_inv f g M N]
  rw [← ModuleSheafTensor.map_comp]
  simp

end FLT.Mazur.FCurve.ModuleLineBundleTensorPullback
namespace FLT.Mazur.FCurve.ModuleLineBundleTensorPullback
variable {X Y : Scheme.{u}}
/-- Transport along equality of scheme maps preserves the tensor comparison. -/
lemma tensorIso_congr {f g : X ⟶ Y} (h : f = g) (M N : Y.Modules) :
    (pullbackCongr h).hom.app (ModuleSheafTensor.tensor M N) ≫
      (tensorIso g M N).hom =
    (tensorIso f M N).hom ≫ ModuleSheafTensor.map
      ((pullbackCongr h).hom.app M) ((pullbackCongr h).hom.app N) := by
  subst g
  simp [pullbackCongr, ModuleSheafTensor.map_id]

/-- Open restriction and pullback identify the same tensor pairing. -/
lemma restrictPullbackTensorIso (f : X ⟶ Y) [IsOpenImmersion f] (M N : Y.Modules) :
    (restrictFunctorIsoPullback f).hom.app (ModuleSheafTensor.tensor M N) ≫
      (tensorIso f M N).hom =
    (ModuleSheafTensor.restrictIso M N f).hom ≫ ModuleSheafTensor.map
      ((restrictFunctorIsoPullback f).hom.app M)
      ((restrictFunctorIsoPullback f).hom.app N) := by
  apply ((restrictAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right]
  change (restrictAdjunction f).homEquiv _ _
    (((restrictAdjunction f).leftAdjointUniq (pullbackPushforwardAdjunction f)).hom.app _) ≫
      _ = _
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  apply ModuleSheafTensor.hom_ext
  intro U m n
  have h := tensorIso_adj_pure f M N U m n
  change (tensorIso f M N).hom.app _
    (((pullbackPushforwardAdjunction f).unit.app _).app U _) = _ at h
  change (tensorIso f M N).hom.app _
    (((pullbackPushforwardAdjunction f).unit.app _).app U _) =
    (ModuleSheafTensor.map _ _).app _
      ((ModuleSheafTensor.restrictIso M N f).hom.app _
        ((ModuleSheafTensor.tensor M N).presheaf.map _ (ModuleSheafTensor.pure M N U m n)))
  rw [h]
  erw [ModuleSheafTensor.pure_restrict M N
    (homOfLE (f.image_preimage_le U)) m n]
  erw [ModuleSheafTensor.restrictIso_hom_pure M N f (f ⁻¹ᵁ U)]
  rw [ModuleSheafTensor.map_pure]
  have unit (P : Y.Modules) (p : Γ(P, U)) :
      ((restrictFunctorIsoPullback f).hom.app P).app (f ⁻¹ᵁ U)
        (P.presheaf.map (homOfLE (f.image_preimage_le U)).op p) =
      ((pullbackPushforwardAdjunction f).unit.app P).app U p :=
    congrArg (fun k ↦ k.app U p)
      (Adjunction.unit_leftAdjointUniq_hom_app (restrictAdjunction f)
        (pullbackPushforwardAdjunction f) P)
  erw [unit M m, unit N n]
end FLT.Mazur.FCurve.ModuleLineBundleTensorPullback

namespace FLT.Mazur.FCurve.ModuleLineBundleTensorPullback
variable {X Y : Scheme.{u}}
/-- The inverse open comparison preserves the tensor pairing. -/
lemma restrictPullbackTensorIso_inv (f : X ⟶ Y) [IsOpenImmersion f] (M N : Y.Modules) :
    (restrictFunctorIsoPullback f).inv.app (ModuleSheafTensor.tensor M N) ≫
      (ModuleSheafTensor.restrictIso M N f).hom =
    (tensorIso f M N).hom ≫ ModuleSheafTensor.map
      ((restrictFunctorIsoPullback f).inv.app M)
      ((restrictFunctorIsoPullback f).inv.app N) := by
  rw [← cancel_epi ((restrictFunctorIsoPullback f).hom.app (ModuleSheafTensor.tensor M N))]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% restrictPullbackTensorIso f M N]
  rw [← ModuleSheafTensor.map_comp]
  simp
end FLT.Mazur.FCurve.ModuleLineBundleTensorPullback

namespace FLT.Mazur.FCurve.ModuleLineBundleTensorPullback
/-- The tensor comparison commutes with every commuting open-immersion square. -/
lemma tensorIso_restrictSquare {X Y Z W : Scheme.{u}}
    (f : X ⟶ Y) (g : Z ⟶ W) (i : Z ⟶ X) (j : W ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] (h : i ≫ f = g ≫ j) (M N : Y.Modules) :
    (restrictFunctor i).map (tensorIso f M N).hom ≫
      (ModuleSheafTensor.restrictIso ((pullback f).obj M) ((pullback f).obj N) i).hom ≫
      ModuleSheafTensor.map (modulePullbackRestrictIso f g i j h M).hom
        (modulePullbackRestrictIso f g i j h N).hom =
    (modulePullbackRestrictIso f g i j h (ModuleSheafTensor.tensor M N)).hom ≫
      (pullback g).map (ModuleSheafTensor.restrictIso M N j).hom ≫
      (tensorIso g (M.restrict j) (N.restrict j)).hom := by
  simp only [modulePullbackRestrictIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_hom, Iso.app_inv, ModuleSheafTensor.map_comp, Category.assoc]
  rw [← reassoc_of% restrictPullbackTensorIso i ((pullback f).obj M) ((pullback f).obj N)]
  rw [reassoc_of% (restrictFunctorIsoPullback i).hom.naturality (tensorIso f M N).hom]
  rw [← reassoc_of% tensorIso_comp_hom i f M N]
  rw [← reassoc_of% tensorIso_congr h M N]
  rw [← reassoc_of% tensorIso_comp_inv g j M N]
  rw [← tensorIso_naturality g
    ((restrictFunctorIsoPullback j).inv.app M) ((restrictFunctorIsoPullback j).inv.app N)]
  rw [← Functor.map_comp_assoc, ← restrictPullbackTensorIso_inv j M N, Functor.map_comp]
  simp only [Category.assoc]
end FLT.Mazur.FCurve.ModuleLineBundleTensorPullback

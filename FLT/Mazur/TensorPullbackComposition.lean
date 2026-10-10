/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleLineBundleTensorPullback
public import FLT.Mazur.SchemeModulePullbackUnitSections

/-!
# Composition coherence of the actual tensor pullback comparison

Two tensor pullbacks agree with the tensor comparison along the composite.
The proof checks the two adjoints on pure sections over every original open.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FLT.Mazur.FCurve.ModuleLineBundleTensorPullback
open ModuleSheafTensor
attribute [local irreducible] ModuleSheafTensor.tensor tensorIso
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A pulled morphism carries the unit of a section to the unit of its image. -/
lemma pullback_map_unit {M N : Y.Modules} (a : M ⟶ N) (U : Y.Opens) (s : Γ(M, U)) :
    ((pullback f).map a).app (f ⁻¹ᵁ U)
        (((pullbackPushforwardAdjunction f).unit.app M).app U s) =
      ((pullbackPushforwardAdjunction f).unit.app N).app U (a.app U s) :=
  congrArg (fun k ↦ k.app U s) ((pullbackPushforwardAdjunction f).unit.naturality a).symm

/-- The tensor pullback comparison respects the actual composition isomorphism. -/
@[reassoc]
lemma tensorIso_comp (M N : Z.Modules) :
    (pullback f).map (tensorIso g M N).hom ≫
        (tensorIso f ((pullback g).obj M) ((pullback g).obj N)).hom ≫
        map ((pullbackComp f g).hom.app M) ((pullbackComp f g).hom.app N) =
      (pullbackComp f g).hom.app (tensor M N) ≫ (tensorIso (f ≫ g) M N).hom := by
  apply ((pullbackPushforwardAdjunction f).homEquiv _ _).injective
  apply ((pullbackPushforwardAdjunction g).homEquiv _ _).injective
  apply ModuleSheafTensor.hom_ext
  intro U m n
  change (map ((pullbackComp f g).hom.app M) ((pullbackComp f g).hom.app N)).app
      ((f ≫ g) ⁻¹ᵁ U)
      ((tensorIso f ((pullback g).obj M) ((pullback g).obj N)).hom.app ((f ≫ g) ⁻¹ᵁ U)
        (((pullback f).map (tensorIso g M N).hom).app ((f ≫ g) ⁻¹ᵁ U)
          (((pullbackPushforwardAdjunction f).unit.app ((pullback g).obj (tensor M N))).app
            (g ⁻¹ᵁ U) (((pullbackPushforwardAdjunction g).unit.app (tensor M N)).app U
              (pure M N U m n))))) =
    (tensorIso (f ≫ g) M N).hom.app ((f ≫ g) ⁻¹ᵁ U)
      (((pullbackComp f g).hom.app (tensor M N)).app ((f ≫ g) ⁻¹ᵁ U)
        (((pullbackPushforwardAdjunction f).unit.app ((pullback g).obj (tensor M N))).app
          (g ⁻¹ᵁ U) (((pullbackPushforwardAdjunction g).unit.app (tensor M N)).app U
            (pure M N U m n))))
  erw [pullback_map_unit f (tensorIso g M N).hom (g ⁻¹ᵁ U)]
  rw [SchemeModulePullbackUnitSections.comp_unit]
  have hg := tensorIso_adj_pure g M N U m n
  change (tensorIso g M N).hom.app (g ⁻¹ᵁ U)
    (((pullbackPushforwardAdjunction g).unit.app (tensor M N)).app U (pure M N U m n)) =
      _ at hg
  rw [hg]
  have hf := tensorIso_adj_pure f ((pullback g).obj M) ((pullback g).obj N) (g ⁻¹ᵁ U)
    (((pullbackPushforwardAdjunction g).unit.app M).app U m)
    (((pullbackPushforwardAdjunction g).unit.app N).app U n)
  change (tensorIso f ((pullback g).obj M) ((pullback g).obj N)).hom.app ((f ≫ g) ⁻¹ᵁ U)
    (((pullbackPushforwardAdjunction f).unit.app
      (tensor ((pullback g).obj M) ((pullback g).obj N))).app (g ⁻¹ᵁ U) _) = _ at hf
  rw [hf]
  erw [ModuleSheafTensor.map_pure]
  rw [SchemeModulePullbackUnitSections.comp_unit,
    SchemeModulePullbackUnitSections.comp_unit]
  exact (tensorIso_adj_pure (f ≫ g) M N U m n).symm

end FLT.Mazur.FCurve.ModuleLineBundleTensorPullback

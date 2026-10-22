/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TensorPowerGeneratorOpen
public import FLT.Mazur.ModuleGlobalSectionPullback

/-!
# Tensor frames commute with arbitrary pullback

The coordinate map for a pair of pulled frames is the pullback of the
original coordinate map. Testing the adjunction on actual pure sections
retains the structure-sheaf scalar map on every open.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor Scheme.Modules.pullback
variable {X Y : Scheme} (f : X ⟶ Y)

/-- The frame on the actual pulled line. -/
def pulledGlobalFrame {M : Y.Modules} (e : M ≅ structureModule Y) :
    (pullback f).obj M ≅ structureModule X :=
  (pullback f).mapIso e ≪≫ modulePullbackUnitIso f

/-- Coordinates of a pulled section are the original coordinate pulled as a function. -/
theorem pulledGlobalFrame_section {M : Y.Modules} (e : M ≅ structureModule Y)
    (U : Y.Opens) (x : Γ(M, U)) :
    (pulledGlobalFrame f e).hom.app (f ⁻¹ᵁ U)
      (((pullbackPushforwardAdjunction f).unit.app M).app U x) =
        f.app U (e.hom.app U x) := by
  have hn := congrArg (fun a ↦ a.app U x)
    ((pullbackPushforwardAdjunction f).unit.naturality e.hom).symm
  change ((pullback f).map e.hom).app (f ⁻¹ᵁ U)
    (((pullbackPushforwardAdjunction f).unit.app M).app U x) =
      ((pullbackPushforwardAdjunction f).unit.app (structureModule Y)).app U
        (e.hom.app U x) at hn
  change (modulePullbackUnitIso f).hom.app _
    (((pullback f).map e.hom).app _ _) = _
  rw [hn]
  exact modulePullbackUnitIso_unit f U _

/-- The actual tensor comparison preserves multiplication of frame coordinates. -/
theorem pulledGlobalFrame_tensor {M N : Y.Modules}
    (e : M ≅ structureModule Y) (v : N ≅ structureModule Y) :
    (tensorIso f M N).hom ≫
      (ModuleSheafTensor.trivialTensorIso (pulledGlobalFrame f e)
        (pulledGlobalFrame f v)).hom =
      (pulledGlobalFrame f (ModuleSheafTensor.trivialTensorIso e v)).hom := by
  apply ((pullbackPushforwardAdjunction f).homEquiv _ _).injective
  apply ModuleSheafTensor.hom_ext
  intro U x y
  change (ModuleSheafTensor.trivialTensorIso (pulledGlobalFrame f e)
    (pulledGlobalFrame f v)).hom.app _
      ((tensorIso f M N).hom.app _
        (((pullbackPushforwardAdjunction f).unit.app _).app U
          (ModuleSheafTensor.pure M N U x y))) =
    (pulledGlobalFrame f (ModuleSheafTensor.trivialTensorIso e v)).hom.app _
      (((pullbackPushforwardAdjunction f).unit.app _).app U
        (ModuleSheafTensor.pure M N U x y))
  erw [tensorIso_adj_pure f M N U x y]
  erw [ModuleSheafTensor.trivialTensorIso_pure,
    pulledGlobalFrame_section f e U x, pulledGlobalFrame_section f v U y,
    pulledGlobalFrame_section f (ModuleSheafTensor.trivialTensorIso e v) U,
    ModuleSheafTensor.trivialTensorIso_pure, map_mul]
  rfl

end FLT.Mazur.FCurve

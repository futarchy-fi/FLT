/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TensorPowerPullbackComparison
public import FLT.Mazur.ModuleTensorPowerSection

/-!
# Tensor-power comparison of a section with a preceding power

The actual pullback comparison carries a pure tensor to the pure tensor of
the compared sections. This retains canonical divisor factors in pole lifts.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor tensorIso
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) {L : Y.Modules} {M : X.Modules}
variable (e : (pullback f).obj L ≅ M)

/-- Pullback and the specified power comparison preserve the original pure factors. -/
theorem tensorPowerPullbackComparison_pure (d : ℕ)
    (s : Γ(L, ⊤)) (t : Γ(tensorPower L d, ⊤)) :
    (tensorPowerPullbackComparison f e (d + 1)).hom.app ⊤
        (pullGlobal f _ (ModuleSheafTensor.pure L (tensorPower L d) ⊤ s t)) =
      ModuleSheafTensor.pure M (tensorPower M d) ⊤
        (e.hom.app ⊤ (pullGlobal f L s))
        ((tensorPowerPullbackComparison f e d).hom.app ⊤ (pullGlobal f _ t)) := by
  rw [tensorPowerPullbackComparison_succ]
  change (ModuleSheafTensor.map e.hom (tensorPowerPullbackComparison f e d).hom).app ⊤
    ((tensorIso f L (tensorPower L d)).hom.app ⊤
      (pullGlobal f _ (ModuleSheafTensor.pure L (tensorPower L d) ⊤ s t))) = _
  have hp : (tensorIso f L (tensorPower L d)).hom.app ⊤
      (pullGlobal f _ (ModuleSheafTensor.pure L (tensorPower L d) ⊤ s t)) =
        ModuleSheafTensor.pure _ _ ⊤ (pullGlobal f L s) (pullGlobal f _ t) :=
    tensorIso_adj_pure f L (tensorPower L d) ⊤ s t
  rw [hp, ModuleSheafTensor.map_pure]

end FLT.Mazur.FCurve

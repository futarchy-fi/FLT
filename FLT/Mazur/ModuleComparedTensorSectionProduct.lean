/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedIsoMultiplication
public import FLT.Mazur.SectionGradedPullback
public import FLT.Mazur.TensorPowerPullbackComparison
public import FLT.Mazur.ModuleGlobalSectionPullback

/-!
# Products of sections under the original tensor-power comparison

Pullback and the specified line comparison preserve the actual homogeneous
section multiplication. No surjectivity of global-section pullback is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor tensorIso
variable {X Y : Scheme} (f : X ⟶ Y) {L : Y.Modules} {M : X.Modules}
variable (e : (pullback f).obj L ≅ M)

/-- The specified pullback comparison preserves every homogeneous global-section product. -/
theorem tensorPowerPullbackComparison_product (d k : ℕ)
    (s : Γ(tensorPower L d, ⊤)) (v : Γ(tensorPower L k, ⊤)) :
    (tensorPowerPullbackComparison f e (d + k)).hom.app ⊤
      (pullGlobal f _ (SectionGradedMultiplication.mul L ⊤ d k s v)) =
        SectionGradedMultiplication.mul M ⊤ d k
          ((tensorPowerPullbackComparison f e d).hom.app ⊤ (pullGlobal f _ s))
          ((tensorPowerPullbackComparison f e k).hom.app ⊤ (pullGlobal f _ v)) := by
  change SectionGradedIso.pieceMap e (d + k) ⊤
    (SectionGradedPullback.pull f L (d + k) ⊤
      (SectionGradedMultiplication.mul L ⊤ d k s v)) =
        SectionGradedMultiplication.mul M ⊤ d k
          (SectionGradedIso.pieceMap e d ⊤ (SectionGradedPullback.pull f L d ⊤ s))
          (SectionGradedIso.pieceMap e k ⊤ (SectionGradedPullback.pull f L k ⊤ v))
  rw [SectionGradedPullback.pull_mul]
  exact SectionGradedIso.pieceMap_mul e ⊤ d k _ _

end FLT.Mazur.FCurve

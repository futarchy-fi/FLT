/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TensorPowerComparedSectionCons
public import FLT.Mazur.SectionGradedAssociativity

/-!
# Sealed section maps of tensor-power comparisons

Keeping the section map opaque avoids expanding the concrete tensor sheaves
when specializing the factor identity to a large geometric construction.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) {L : Y.Modules} {M : X.Modules}
variable (e : (pullback f).obj L ≅ M)

/-- Transport global sections through the specified actual power comparison. -/
irreducible_def tensorPowerComparedSection (d : ℕ) (t : Γ(tensorPower L d, ⊤)) :
    Γ(tensorPower M d, ⊤) :=
  (tensorPowerPullbackComparison f e d).hom.app ⊤ (pullGlobal f _ t)

/-- A specified section factor is retained through the sealed transport. -/
theorem tensorPowerComparedSection_cons (d : ℕ) (s : Γ(L, ⊤)) (v : Γ(M, ⊤))
    (hs : e.hom.app ⊤ (pullGlobal f L s) = v) (t : Γ(tensorPower L d, ⊤)) :
    tensorPowerComparedSection f e (d + 1) (SectionGradedMultiplication.cons L d ⊤ s t) =
      SectionGradedMultiplication.cons M d ⊤ v (tensorPowerComparedSection f e d t) := by
  rw [tensorPowerComparedSection_def, tensorPowerComparedSection_def]
  exact (tensorPowerPullbackComparison_pure f e d s t).trans
    (congrArg (fun a ↦ ModuleSheafTensor.pure M (tensorPower M d) ⊤ a
      ((tensorPowerPullbackComparison f e d).hom.app ⊤ (pullGlobal f _ t))) hs)

end FLT.Mazur.FCurve

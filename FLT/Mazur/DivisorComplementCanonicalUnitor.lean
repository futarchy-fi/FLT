/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorComplementCanonical

/-!
# Canonical degree-one sections on the Cartier complement

A first-power section whose tensor unitor is the original canonical section
represents the constant function one on the actual complement.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] divisorLineBundle ModuleSheafTensor.tensor

variable {X : Scheme} {I : X.IdealSheafData} (hI : EffectiveCartier I)

/-- The first tensor power of the canonical section is recognized by its unitor. -/
theorem divisorComplementFunction_one_of_unitor
    (z : Γ(tensorPower (divisorLineBundle I hI) 1, ⊤))
    (hz : (ModuleSheafTensor.rightUnitor (divisorLineBundle I hI)).hom.app ⊤ z =
      divisorSection hI ⊤) :
    divisorComplementFunction hI 1 z = 1 := by
  have he : z = tensorPowerSection (divisorLineBundle I hI) ⊤
      (divisorSection hI ⊤) 1 := by
    apply (ConcreteCategory.bijective_of_isIso
      ((ModuleSheafTensor.rightUnitor (divisorLineBundle I hI)).hom.app ⊤)).injective
    rw [hz]
    exact ((ModuleSheafTensor.rightUnitor_pure _ ⊤
      (1 : Γ(X, ⊤)) (divisorSection hI ⊤)).trans
      (one_smul _ _)).symm
  rw [he, divisorComplementFunction_power]

end FLT.Mazur.FCurve

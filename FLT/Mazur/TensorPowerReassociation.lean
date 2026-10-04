/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeVeryAmpleLineBundle
public import FLT.Mazur.ModuleSheafTensorAssociator

/-!
# Addition and multiplication of tensor-power exponents

These are isomorphisms of the actual sheafified tensor powers, including
exponent zero. They allow sections of iterated powers to share one degree.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve.ModuleLineBundleTensorPullback
open ModuleSheafTensor
variable {X : Scheme.{u}} (L : X.Modules)

/-- Tensoring two powers adds their exponents. -/
def tensorPowerAddIso : ∀ m n : ℕ,
    tensor (tensorPower L m) (tensorPower L n) ≅ tensorPower L (m + n)
  | 0, n => leftUnitor (tensorPower L n) ≪≫ eqToIso (congrArg (tensorPower L) (Nat.zero_add n).symm)
  | m + 1, n =>
    ModuleSheafTensorAssociator.associator L (tensorPower L m) (tensorPower L n) ≪≫
      congr (Iso.refl L) (tensorPowerAddIso m n) ≪≫ eqToIso (by
        change tensorPower L (m + n + 1) = tensorPower L (m + 1 + n)
        congr 1
        omega)

/-- Iterating natural tensor powers multiplies their exponents. -/
def tensorPowerMulIso (m : ℕ) : ∀ n : ℕ,
    tensorPower (tensorPower L m) n ≅ tensorPower L (m * n)
  | 0 => eqToIso (by
      change structureModule X = tensorPower L (m * 0)
      rw [Nat.mul_zero]
      rfl)
  | n + 1 => congr (Iso.refl _) (tensorPowerMulIso m n) ≪≫
      tensorPowerAddIso L m (m * n) ≪≫ eqToIso (by rw [Nat.mul_succ, Nat.add_comm])

end FLT.Mazur.FCurve.ModuleLineBundleTensorPullback
